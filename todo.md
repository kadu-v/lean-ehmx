# 述語条件付き操作の実装計画

目標は `op : ∀β. P ⇒ A → B` を EHM(X) に追加し、ATTAPL 10.4.4・10.4.8・429–430頁に対応する推論三定理と、操作捕捉を含む保存・進行・効果安全性を維持すること。述語条件付き操作は EHM(X) 固有の拡張である。操作の矢印に効果欄は追加しない。

## 構文と意味

- [x] `OpDecl.condition : Constraint := .truth` を追加し、既存フィールドと構造的比較を維持する。
- [x] `Constraint`・`Scheme` の自由型・効果変数集合と必要な `BEq` を追加する。
- [x] 宣言条件に `WF S kinds 0`・自由項変数なし・自由型効果変数なしを要求する。条件の充足可能性は要求しない。内部の量化と局所スキーム定義を許す。
- [x] `Constraint.implies P D` と通常の論理含意の意味を追加する。前件には `WF S Δ 0` と `fpi = ∅` を要求する。
- [x] shift・代入・自由変数・意味解釈・相互帰納法に含意を追加する。

## 条件の代入と意味保存

- [x] 宣言条件の外側代入不変性・具体化と代入の交換・割当て列の追加不変性を証明する。
- [x] 含意の意味保存・整形式性・項環境への非依存を証明する。
- [x] `groundMonotonicity` を整形式制約・スキームに限定して証明し、`definitionMonotone` と多相 let 完全性を更新する。

## 型付けと操作保存

- [x] `Typing.perform` に同じ型効果引数で具体化した条件の含意を要求する。
- [x] `Typing.handle` の操作節を `shift C ∧ P` の下で検査する。
- [x] 型効果代入・制約強化・項弱化・値代入で条件を保持する。
- [x] `operationClauseInstantiation` を `C ∧ P[args]` の具体化と呼出側の条件充足で証明する。
- [x] `operationClauseShift`・`ContextTyping`・`operationElimination` を更新し、存在引数と条件を作用域内で保持する。
- [x] 操作保存・一歩多歩保存・進行・到達状態の効果安全性を検証する。

## 生成と推論三定理

- [x] perform の既存の存在量化内に条件の連言を追加する。
- [x] handler の操作節を `∀β. P ⇒ 節の生成制約` にする。前件は項束縛導入の前に置き、外側の環境実現可能性は含意の外に維持する。
- [x] 生成の整形式性・作用域・代入・単調性・環境との交換を拡張する。
- [x] 健全性の perform と handler 分岐を証明する。
- [x] 完全性の perform と handler 分岐を証明する。
- [x] 主要制約性と型クラスモデルへの特殊化を検証する。

## 回帰

- [x] truth 条件と既存の型付け・生成制約の対応、および既存回帰。
- [x] Eq 条件付き操作の Int・Bool・条件付きリスト利用、Ord からの条件充足。
- [x] 操作節 `let _ = eq z z in k z` で宣言条件からメソッド利用を型付け。
- [x] `eq (perform op x) y` の handler 全体の空効果直接型付け、推論三定理、Int による生成制約充足。
- [x] 混合 kind、条件内の存在全称量化、局所スキーム定義、外側文脈 shift。
- [x] 未充足クラス条件・false 条件の呼出しの充足不能性。
- [x] false 条件の宣言整形式性と操作節の条件付き検査。
- [x] 自由型効果変数・外側項変数・範囲外束縛・kind 不一致の拒否。
- [x] 条件を使う実際の操作捕捉への保存適用と、存在量化・制約強化を経由する保存。
- [x] 新規回帰を標準 `import EHMX` とビルド対象に追加。

## 最終検証と文書

- [x] `lake build`。
- [x] `tests/EHMXGoals.lean` の既存 Goal 型検査。
- [x] `tests/EHMXInference.lean` の推論回帰。
- [x] `tests/EHMXAxioms.lean` の全 EHMX 定理公理監査。sorry・追加公理なし。
- [x] `git diff --check`。
- [x] 検査成功後に README・EHMX 仕様・型クラス説明・既存証明 TODO を更新。
- [x] 最終検査結果と残る課題を本ファイルに記録。

`EffectFramework` に公理を追加せず、最終 Goal に条件の非空性・ソルバー・追加実現可能性を要求しない。HMX・実行時構文・簡約規則は変更しない。パーサー・辞書変換・探索器・ソルバー・PDF 作業は対象外。

## 完了記録（2026-10-18）

全項目について Lean の証明と検査が成功した。主な証拠は以下のとおり。

- 構文・意味：`OpDecl.condition`、`Constraint.implies`、`Constraint.fv`、`Scheme.fv`、`Constraint.WF`、`Constraint.Holds`。
- 条件の代入：`substBoundCongruence`、`declarationConditionSubstBound`、`declarationConditionOpenSubstBound`、`conditionDeclarationAppend`、`conditionDeclarationOpen`。含意は `substBoundWF`・`substBoundSemantics`・`groundAgreement` に含めた。
- 環境：整形式性を前提にした `groundMonotonicity`・`definitionMonotone`、環境実現可能性を残す `envLetInImplication`。完全性で必要な整形式性は型付け導出から得る。
- 保存と推論：`operationClauseInstantiation`、`operationClauseShift`、`operationElimination`、`operationPreservation`、`preservation`、`preservationSteps`、`effectSafety`、`emptyEffectSafety`、`inferenceSoundness`、`inferenceCompleteness`、`constraintGenerationPrincipality`。最終 Goal と EffectFramework の変更はない。
- 回帰：[ConditionalOperationsRegression.lean](EHMX/ConditionalOperationsRegression.lean) の `intCall`・`boolCall`・`conditionalListCall`・`ordCall`、`clauseFromCondition`、`handledMethodTyping` と推論三定理・充足可能性、`capturePreserved`・`existentialArgumentCapturePreserved`、混合条件と局所定義、false と未充足クラス、不正宣言の拒否。`Typing.performTruth`・`Typing.handleTruth` と生成式の意味的同値で truth 条件の互換性を検査。

検査：`lake build`（840 jobs）、`lake env lean tests/EHMXGoals.lean`、`lake env lean tests/EHMXInference.lean`、`lake env lean tests/EHMXAxioms.lean`（1195定理宣言）、`git diff --check` が成功。監査の許容公理は `propext`・`Classical.choice`・`Quot.sound` のみ。

残る課題：本計画の実装・証明・検証に未完了項目はない。次に必要な証明義務はない。既存 TODO の追加回帰は本計画と別に保持した。PDF の更新・再生成・整合性検査は実施していない。
