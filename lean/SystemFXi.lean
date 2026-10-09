import SystemFXi.Safety
import SystemFXi.EffectPolySafety
import SystemFXi.EffectPolyExamples
import SystemFXi.EHMX.Examples
import SystemFXi.EHMX.Completeness
import SystemFXi.EHMX.PureUnification
import SystemFXi.EHMX.PrincipalScheme
import SystemFXi.EHMX.ConstraintSystem
import SystemFXi.EHMX.GenericInference
import SystemFXi.EHMX.GenericPrincipal
import SystemFXi.EHMX.GenericCompleteness
import SystemFXi.EHMX.GenericSupport
import SystemFXi.EHMX.GenericEffectFresh
import SystemFXi.EHMX.GenericOrigin
import SystemFXi.EHMX.GenericOriginInduction
import SystemFXi.EHMX.GenericHandlerBridge
import SystemFXi.EHMX.GenericHandlerScope
import SystemFXi.EHMX.GenericHandlerSuccess
import SystemFXi.EHMX.GenericFullCompleteness
import SystemFXi.EHMX.SequentialNormalizer
import SystemFXi.EHMX.GenericHandlerFree
import SystemFXi.EHMX.GenericEmbedding

/-!
# System Fξ

旧形式の `SystemFXi.Safety` と、効果変数を持つ
`SystemFXi.Poly.effect_safety` までの全モジュールを公開する。

* `SystemFXi.Syntax`, `Substitution`, `Typing`, `Semantics` — 言語の定義
* `SystemFXi.Subtyping`, `TypeLemmas`, `TermLemmas` — 基本補題
* `SystemFXi.Progress`, `Preservation`, `Safety` — 型安全性と効果安全性
* `SystemFXi.EffectPoly*` — kind `T` と `E` の同時置換、効果多相な型安全性
* `SystemFXi.EHMX.*` — 集合効果 handler と静的述語を持つ表層言語の制約生成・健全性・完全性・主要計算型スキーム
-/
