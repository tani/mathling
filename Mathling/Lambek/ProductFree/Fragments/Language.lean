    module

    import Mathling.Lambek.ProductFree.Fragments.Shallow.Core
    import Mathling.Lambek.ProductFree.Fragments.Left.Shallow.Core
    import Mathling.Lambek.ProductFree.Fragments.Right.Shallow.Core
    public import Mathling.Grammar.Regular.Linear
    public import Mathling.Grammar.Regular.Left
    public import Mathling.Grammar.Regular.Right

    import LiterateLean
    open scoped LiterateLean


# Shallow Lambek 断片が表す言語クラス

このモジュールは、三つの shallow 断片を言語クラスの側から公開する。一般の
shallow 断片には線形文法を、左または右だけを持つ shallow 断片には対応する
左線形文法または右線形文法を結び付ける。

現在の層は意味論的なプレゼンテーション境界である。既存の Core モジュールにある
シーケント計算は変更せず、文法と言語クラスの対応だけを公開する。単語からカテゴリを
選ぶ有限語彙と、選ばれたカテゴリ列の導出可能性を結ぶ語彙層は、この境界の上に
追加される別の責務である。

Lambek 計算では前提が空にならない。そのため、ここで扱う各プレゼンテーションは
空語を含まないという証拠を保持する。

```mermaid
flowchart LR
    Shallow["Shallow"] <--> Linear["Linear grammar"]
    Left["Left.Shallow"] <--> LeftLinear["Left-linear grammar"]
    Right["Right.Shallow"] <--> RightLinear["Right-linear grammar"]
    Linear --> ClassLinear["Linear language"]
    LeftLinear --> ClassRegular["Regular language"]
    RightLinear --> ClassRegular
```

## 一般 shallow 断片

最初に、一般 shallow 断片の言語プレゼンテーションを定義する。この断片では左右の
除法をともに許すため、対応先は左右どちらにも一個の非終端記号を置ける線形文法である。

以下の名前空間は、既存の shallow 型とシーケントに対応する言語 API の所属先を固定する。

```lean
namespace Mathling.Lambek.ProductFree.Shallow
```

プレゼンテーションは線形文法本体と空語排除の証拠を一緒に保持する。これにより、
後続の定理は空語に関する仮定を外部状態に頼らず、値そのものから取り出せる。

```lean
/-- An epsilon-free linear-language presentation for the shallow fragment. -/
public structure Grammar (T : Type*) where
  presentation : Mathling.Grammar.LinearGrammar T
  empty_not_mem : [] ∉ presentation.language
```

以降の操作はプレゼンテーション型のメソッドとして公開するため、専用の名前空間に置く。

```lean
namespace Grammar

variable {T : Type*}
```

言語の意味は、保持している線形文法の言語をそのまま観測することで与える。この定義が
後続の変換定理における共通の観測点になる。

```lean
/-- The language represented by a shallow presentation. -/
@[expose] public def language (g : Grammar T) : Language T :=
  g.presentation.language
```

次に shallow という境界を忘れ、内部の線形文法を取り出す。終端記号や生成規則を
書き換えない忘却変換なので、データ変換による失敗は起こらない。

```lean
/-- Forget the shallow boundary and recover the linear grammar. -/
/- Exposed because the public preservation theorem reduces this forgetful map. -/
@[expose]
public def toLinearGrammar (g : Grammar T) : Mathling.Grammar.LinearGrammar T :=
  g.presentation
```

言語の定義と忘却変換が同じ文法を参照するため、言語保存は定義的等式になる。この等式が
以後のクラス定理で shallow 側と線形文法側を接続する。

```lean
@[important, grind =, simp] public theorem toLinearGrammar_language (g : Grammar T) :
    g.toLinearGrammar.language = g.language := rfl
```

忘却先は線形文法なので、その既存定理を用いてプレゼンテーションの言語が線形言語で
あることを得る。これは最終的な iff の shallow から linear への向きを担う。

```lean
@[important, grind .] public theorem language_isLinear (g : Grammar T) :
    g.language.IsLinear :=
  g.toLinearGrammar.language_isLinear
```

構造体に保存した不変条件を、言語 API 上の定理として取り出す。最終的な存在同値では、
この条件と対象言語に対する仮定が一致する。

```lean
@[important, grind .] public theorem language_empty_not_mem (g : Grammar T) :
    [] ∉ g.language :=
  g.empty_not_mem
```

一般 shallow 側の観測 API が揃ったので、二つの名前空間を閉じる。

```lean
end Grammar
end Mathling.Lambek.ProductFree.Shallow
```

### 線形文法から一般 shallow への変換

逆向きは線形文法の名前空間に置き、メソッド記法で利用できるようにする。変換は文法を
変更せず、呼び出し側が与えた空語排除の証拠を shallow 境界に格納する。

```lean
namespace Mathling.Grammar.LinearGrammar

variable {T : Type*}
```

この構成によって任意の epsilon-free 線形文法が一般 shallow のプレゼンテーションに
なる。証拠引数は実行時のデータではなく、Lambek 側の非空条件を記録する契約である。

```lean
/-- Regard an epsilon-free linear grammar as a shallow presentation. -/
/- Exposed because the public preservation theorem reduces the packaged grammar. -/
@[expose]
public def toShallowGrammar (g : Mathling.Grammar.LinearGrammar T)
    (empty_not_mem : [] ∉ g.language) :
    Mathling.Lambek.ProductFree.Shallow.Grammar T where
  presentation := g
  empty_not_mem := empty_not_mem
```

変換後も同じ文法を保持するので、この向きの言語保存も定義的等式である。先ほどの
忘却変換と合わせて、一般 shallow と epsilon-free 線形文法を往復できる。

```lean
@[important, grind =, simp] public theorem toShallowGrammar_language
    (g : Mathling.Grammar.LinearGrammar T) (empty_not_mem : [] ∉ g.language) :
    (g.toShallowGrammar empty_not_mem).language = g.language := rfl
```

```lean
end Mathling.Grammar.LinearGrammar
```

## left-shallow 断片

left-shallow では左除法だけを許す。この方向制約を文法側でも保つため、内部表現には
左線形文法を使う。正規言語の既存特徴付けが有限個の非終端記号を要求するので、その
有限性証拠もプレゼンテーションに含める。

```lean
namespace Mathling.Lambek.ProductFree.Left.Shallow
```

一般 shallow と同様に空語排除を保持し、さらに左線形文法の非終端記号型が有限である
ことを存在的な Fintype インスタンスとして保存する。

```lean
/-- An epsilon-free finite left-linear presentation. -/
public structure Grammar (T : Type*) where
  presentation : Mathling.Grammar.LeftLinearGrammar T
  finiteNonterminals : Nonempty (Fintype presentation.cfg.NT)
  empty_not_mem : [] ∉ presentation.language
```

```lean
namespace Grammar

variable {T : Type}
```

left-shallow の言語観測も、保持している左線形文法の言語そのものである。

```lean
@[expose] public def language (g : Grammar T) : Language T :=
  g.presentation.language
```

方向制約を失わない忘却変換として、内部の左線形文法を取り出す。

```lean
/- Exposed because the public preservation theorem reduces this forgetful map. -/
@[expose]
public def toLeftLinearGrammar (g : Grammar T) :
    Mathling.Grammar.LeftLinearGrammar T :=
  g.presentation
```

観測対象と忘却先が同一なので、言語保存は定義的に成立する。

```lean
@[important, grind =, simp] public theorem toLeftLinearGrammar_language
    (g : Grammar T) : g.toLeftLinearGrammar.language = g.language := rfl
```

有限終端アルファベットのもとで、既存の左線形文法による特徴付けに文法と有限性証拠を
渡す。これにより left-shallow の言語が正規である方向が得られる。

```lean
@[important, grind .] public theorem language_isRegular [Finite T] (g : Grammar T) :
    g.language.IsRegular := by
  apply Mathling.Grammar.Language.isRegular_iff_exists_leftLinearGrammar.mpr
  exact ⟨g.toLeftLinearGrammar, g.finiteNonterminals, rfl⟩
```

最後に、この片側断片でも空語が言語に含まれないことを公開 API として取り出す。

```lean
@[important, grind .] public theorem language_empty_not_mem (g : Grammar T) :
    [] ∉ g.language :=
  g.empty_not_mem
```

```lean
end Grammar
end Mathling.Lambek.ProductFree.Left.Shallow
```

### 左線形文法から left-shallow への変換

逆変換は左線形文法、有限性証拠、空語排除証拠を一つの left-shallow 値へ束ねる。

```lean
namespace Mathling.Grammar.LeftLinearGrammar

variable {T : Type}
```

```lean
/-- Regard an epsilon-free finite left-linear grammar as left-shallow. -/
/- Exposed because the public preservation theorem reduces the packaged grammar. -/
@[expose]
public def toLeftShallowGrammar (g : Mathling.Grammar.LeftLinearGrammar T)
    (finiteNonterminals : Nonempty (Fintype g.cfg.NT))
    (empty_not_mem : [] ∉ g.language) :
    Mathling.Lambek.ProductFree.Left.Shallow.Grammar T where
  presentation := g
  finiteNonterminals := finiteNonterminals
  empty_not_mem := empty_not_mem
```

この変換も文法本体を変更しないため、言語保存は rfl で閉じる。これが正規言語から
left-shallow の存在証人を作る際の最後の変換になる。

```lean
@[important, grind =, simp] public theorem toLeftShallowGrammar_language
    (g : Mathling.Grammar.LeftLinearGrammar T)
    (finiteNonterminals : Nonempty (Fintype g.cfg.NT))
    (empty_not_mem : [] ∉ g.language) :
    (g.toLeftShallowGrammar finiteNonterminals empty_not_mem).language = g.language := rfl
```

```lean
end Mathling.Grammar.LeftLinearGrammar
```

## right-shallow 断片

right-shallow は left-shallow の鏡像であり、右除法だけを許す。語順の向きを反転で
隠さず、右線形文法との対応を独立した API として公開する。

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow
```

構造は left-shallow と対称で、右線形文法、有限非終端記号の証拠、空語排除の証拠を
保持する。

```lean
/-- An epsilon-free finite right-linear presentation. -/
public structure Grammar (T : Type*) where
  presentation : Mathling.Grammar.RightLinearGrammar T
  finiteNonterminals : Nonempty (Fintype presentation.cfg.NT)
  empty_not_mem : [] ∉ presentation.language
```

```lean
namespace Grammar

variable {T : Type}
```

```lean
@[expose] public def language (g : Grammar T) : Language T :=
  g.presentation.language
```

右方向の形を保ったまま、内部の右線形文法を取り出す。

```lean
/- Exposed because the public preservation theorem reduces this forgetful map. -/
@[expose]
public def toRightLinearGrammar (g : Grammar T) :
    Mathling.Grammar.RightLinearGrammar T :=
  g.presentation
```

```lean
@[important, grind =, simp] public theorem toRightLinearGrammar_language
    (g : Grammar T) : g.toRightLinearGrammar.language = g.language := rfl
```

有限終端アルファベットと有限非終端記号を既存の右線形特徴付けへ渡し、
right-shallow の言語が正規であることを得る。

```lean
@[important, grind .] public theorem language_isRegular [Finite T] (g : Grammar T) :
    g.language.IsRegular := by
  apply Mathling.Grammar.Language.isRegular_iff_exists_rightLinearGrammar.mpr
  exact ⟨g.toRightLinearGrammar, g.finiteNonterminals, rfl⟩
```

```lean
@[important, grind .] public theorem language_empty_not_mem (g : Grammar T) :
    [] ∉ g.language :=
  g.empty_not_mem
```

```lean
end Grammar
end Mathling.Lambek.ProductFree.Right.Shallow
```

### 右線形文法から right-shallow への変換

左側と同じデータフローを右線形文法について構成する。

```lean
namespace Mathling.Grammar.RightLinearGrammar

variable {T : Type}
```

```lean
/-- Regard an epsilon-free finite right-linear grammar as right-shallow. -/
/- Exposed because the public preservation theorem reduces the packaged grammar. -/
@[expose]
public def toRightShallowGrammar (g : Mathling.Grammar.RightLinearGrammar T)
    (finiteNonterminals : Nonempty (Fintype g.cfg.NT))
    (empty_not_mem : [] ∉ g.language) :
    Mathling.Lambek.ProductFree.Right.Shallow.Grammar T where
  presentation := g
  finiteNonterminals := finiteNonterminals
  empty_not_mem := empty_not_mem
```

言語保存定理により、変換を介しても対象の正規言語が変わらないことを固定する。

```lean
@[important, grind =, simp] public theorem toRightShallowGrammar_language
    (g : Mathling.Grammar.RightLinearGrammar T)
    (finiteNonterminals : Nonempty (Fintype g.cfg.NT))
    (empty_not_mem : [] ∉ g.language) :
    (g.toRightShallowGrammar finiteNonterminals empty_not_mem).language = g.language := rfl
```

```lean
end Mathling.Grammar.RightLinearGrammar
```

## 言語クラスとしての iff

ここまでで各方向の変換と包含が揃った。最後に対象言語 L が空語を含まないという仮定の
もとで、それぞれのプレゼンテーションが存在することと既存の言語クラス述語が同値で
あることをまとめる。

### shallow と線形言語

順方向では既存の線形文法存在定理から文法を取り出し、空語排除を言語等式に沿って
移送して shallow プレゼンテーションを作る。逆方向では、先に証明した
language_isLinear をそのまま使う。

```lean
namespace Language

variable {T : Type*}
```

```lean
@[important, grind =] public theorem isLinear_iff_exists_shallowGrammar
    {L : Language T} (empty_not_mem : [] ∉ L) :
    L.IsLinear ↔
      ∃ g : Mathling.Lambek.ProductFree.Shallow.Grammar T, g.language = L := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Language.isLinear_iff_exists_linearGrammar.mp h
    have hne : [] ∉ g.language := by
      intro hempty
      exact empty_not_mem (by simpa [hg] using hempty)
    exact ⟨g.toShallowGrammar hne, by simpa using hg⟩
  · rintro ⟨g, rfl⟩
    exact g.language_isLinear
```

```lean
end Language
```

### 片側 shallow と正規言語

正規言語側の既存 iff は Mathling.Grammar.Language 名前空間にあるため、新しい二定理も
同じ場所へ置く。終端アルファベットの有限性は既存定理の契約をそのまま引き継ぐ。

```lean
namespace Mathling.Grammar.Language

variable {T : Type}
```

left-shallow の定理では、左線形文法と有限非終端記号の証拠を既存 iff から同時に
取り出す。対象言語との等式を使って空語排除を移送し、先ほどの逆変換へ渡す。

```lean
@[important, grind =] public theorem isRegular_iff_exists_leftShallowGrammar
    [Finite T] {L : Language T} (empty_not_mem : [] ∉ L) :
    L.IsRegular ↔
      ∃ g : Mathling.Lambek.ProductFree.Left.Shallow.Grammar T, g.language = L := by
  constructor
  · intro h
    obtain ⟨g, hfinite, hg⟩ := isRegular_iff_exists_leftLinearGrammar.mp h
    have hne : [] ∉ g.language := by
      intro hempty
      exact empty_not_mem (by simpa [hg] using hempty)
    refine ⟨g.toLeftShallowGrammar hfinite hne, ?_⟩
    exact (g.toLeftShallowGrammar_language hfinite hne).trans hg
  · rintro ⟨g, rfl⟩
    exact g.language_isRegular
```

right-shallow も同じデータフローを右線形文法について適用する。二つの定理を別々に
公開することで、利用者は語順の向きを反転せずに必要な断片を選択できる。

```lean
@[important, grind =] public theorem isRegular_iff_exists_rightShallowGrammar
    [Finite T] {L : Language T} (empty_not_mem : [] ∉ L) :
    L.IsRegular ↔
      ∃ g : Mathling.Lambek.ProductFree.Right.Shallow.Grammar T, g.language = L := by
  constructor
  · intro h
    obtain ⟨g, hfinite, hg⟩ := isRegular_iff_exists_rightLinearGrammar.mp h
    have hne : [] ∉ g.language := by
      intro hempty
      exact empty_not_mem (by simpa [hg] using hempty)
    refine ⟨g.toRightShallowGrammar hfinite hne, ?_⟩
    exact (g.toRightShallowGrammar_language hfinite hne).trans hg
  · rintro ⟨g, rfl⟩
    exact g.language_isRegular
```

すべてのクラス同値が閉じたので、正規言語の名前空間を閉じる。

```lean
end Mathling.Grammar.Language
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
