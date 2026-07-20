    module

    public import Lean.Attributes

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Meta / Important モジュール

このモジュールは注釈専用の `@[important]` タグ属性を定義する。宣言にこの属性を
付与しても、環境・型検査・他のいかなる戦術の挙動にも影響しない。ライブラリの読者が
特に注目すべき定理や定義を目視で選び出すための、純粋に文書化目的の目印である。

登録結果は Lean 環境内の tag 集合としてだけ保持される。宣言 $`d`$ について
`importantAttr.hasTag env d` を照会できるが、タグは $`d`$ の型、simp 属性、生成コードを
変えない。登録は初期化時に一度だけ行われる。

```lean
@[expose] public section

namespace Mathling.Meta

/-- A no-op tag attribute: `@[important]` marks a declaration as noteworthy for
readers. It has no effect on elaboration, `simp`, or any other tactic — it only
records that the declaration was tagged. Query tagged declarations with
`Mathling.Meta.importantAttr.hasTag`. -/
initialize importantAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `important
    "marks a declaration as important; purely documentational, has no effect"

end Mathling.Meta

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
