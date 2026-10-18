# EHMX の構文 型付け 制約生成と証明状況

EHMX は、抽象的な制約モデル X に基づく HM(X) に、代数的効果の操作、deep handler、値制限付き let を加えた体系である。**効果付き進行性、型・効果代入、スキーム値代入、操作捕捉を含む一歩・多歩保存、任意の到達状態の効果安全性を証明した。推論の健全性・完全性・主要制約性も、既存の Goal の前提・結論を維持して証明した。**

## 1 目標と出典

制約生成の健全性は ATTAPL 第10章の定理10.4.4、完全性は定理10.4.8、主要制約性は429–430頁の説明に対応する EHMX 拡張である。ATTAPL §10.5の型安全性とは別に、handler を含む評価に対する保存と効果付き進行性を証明する。既存 HMX の証明を、拡張構文にそのまま適用したとは主張しない。

操作・handler の参照は lean-system-f-xi のコミット 9173a02d9c67eea0b0c665d3319d834e3947518f、SystemFXi.Poly の EffectPolyTyping、EffectPolySemantics、EffectPolyPreservation、EffectPolySafety である。同リポジトリには let がないため、let の型付け・推論・簡約は EHMX で追加した。参照先の明示的な型抽象・型適用、高階の多相型は EHMX の項構文には含めない。

## 2 構文と束縛

項は変数、lambda 抽象、適用、let、perform、handle からなる。handler は return 節と一つの操作節を持つ。値は変数と lambda 抽象だけである。関数型は引数型、潜在効果、結果型の三つの成分を持つ。

型 kind は0、効果 kind は1である。型・効果は同じ生の構文 Ty で表し、Ty.HasKind で区別する。効果の構成子は空集合、操作ラベルの単集合、和集合であり、効果変数も許す。X は追加の kind、型構成子、述語を持てる。

項変数と型・効果変数には別の添字列を使う。自由変数は名前、束縛変数は de Bruijn 添字で表す。項の return 節では添字0が戻り値、操作節では添字0が継続 k、添字1が操作引数 x である。操作宣言の量化変数は種類のリストの先頭から添字0、1、…となる。

OpSignature.WF は、各宣言の量化変数が宣言された kind を持ち、引数型・結果型がその量化変数の下で kind 0を持ち、自由な型・効果変数を含まないことを要求する。操作宣言は型変数と効果変数を混在して量化できる。

## 3 制約モデル

Model は kind ごとの値、構成子の解釈、述語、部分順序、効果値の操作集合としての解釈を与える。EffectFramework は kind の非空性、構成子の kind 保存、部分順序の反射律・推移律・反対称律、有限集合効果の包含、空集合・単集合・和集合の解釈、関数型の順序を要求する。

関数型の順序は引数に反変、結果と潜在効果に共変である。保存の目標には、追加の非関数構成子が関数型の下に入らない ArrowSeparated を明記する。これらの前提に、型付け・推論・保存・進行の結論は含めない。

Concrete.framework は、基底型と構造的な効果付き関数型、有限集合効果からなる具体モデルについて、すべての EffectFramework の前提を証明する。Concrete.arrowSeparated も証明済みである。具体モデルの成立は、体系全体の保存定理の証明とは異なる。

制約は真・偽・原子・連言・存在量化・全称量化・スキームの束縛・変数のインスタンス化を持つ。全称制約は、指定 kind を満たすすべての値の組について成立することを要求する。型スキームの全称記号は、具体化できる型の上方閉集合を定めるものであり、全称制約とは意味が異なる。

## 4 型付け

Typing の引数は型シグネチャ S、モデル M、操作シグネチャ sig、型・効果変数の文脈 Delta、制約 C、項環境 Gamma、項 e、結果型 T、評価効果 eps である。JudgmentWF は制約・環境・型・効果の整形式性と項の作用域を要求する。外側の制約と環境のスキームは自由な項識別子に依存しない。

変数はスキームを具体化し、評価効果は空集合となる。lambda の本体の効果は関数型の潜在効果となり、lambda 自体の評価効果は空集合となる。適用の効果は関数式、引数式、潜在効果の和集合である。

letMono は右辺の型を単相で共有し、右辺と本体の効果を合併する。この規則は右辺が値の場合にも適用できる。letPoly は右辺が値の場合だけ適用し、右辺を空効果で検査する。新しく一般化する変数は外側の文脈の前に導入し、外側の制約と環境を shift する。一般化の制約に存在する具体化があることを含意として要求する。

perform は宣言の型・効果引数を具体化して引数を検査し、評価効果に操作ラベルを追加する。項に型・効果引数は保存しない。

handle は入力 A ! epsIn、出力 B ! epsOut に対し、epsIn が {op} と epsOut の和集合に含まれることを要求する。return 節は x:A の下で B ! epsOut を持つ。操作節は宣言の量化変数を任意のものとして、x:OpArg と k:(OpResult ->[epsOut] B) の下で検査する。外側の B、epsOut、制約、環境は量化変数の分だけ shift される。操作節の変数を外側へ漏らさない。

部分型・効果包含、制約の強化、型・効果変数の存在量化を型付け規則として持つ。存在量化の除去・反転では、内側で使う型を外側へ勝手に取り出してはならない。

## 5 評価

左から右の値呼び評価を行う。let は右辺だけを先に評価し、値になった時点で本体へ捕獲回避代入する。操作引数も値になるまで評価する。

handler は最も内側の対応する操作を捕捉する。捕捉する操作が途中の評価文脈で既に処理されていないことを、EvalCtx.handled により検査する。再開する継続は lambda y. handle E[y] with h であり、元の handler を再設置する deep handler である。操作節そのものを自動的に同じ handler の内側へ置くことはしない。

操作節への同時代入は [継続, 引数値] の順序で行う。継続の lambda の下へ移る際には、捕捉した文脈、return 節、操作節の外側の変数をそれぞれ正しい束縛深さで shift する。型・効果の引数は実行時には存在しない。

## 6 制約生成

generate sig e T eps は、要求型 T と評価効果上界 eps に対する制約を構文再帰で生成する。infer sig Gamma e T eps は環境のスキーム束縛とその実現可能性を付加する。型・効果の内部変数は束縛添字で導入するため、自由名の新鮮性を選ぶ処理は不要である。

値 let は右辺を空効果で生成し、その結果型をスキーム化する。非値 let は右辺と本体の両方の外側に型・効果変数を存在量化し、一つの単相型を共有する。handler は入力型・入力効果・内部出力型・内部出力効果を存在量化し、操作節の制約だけを宣言の変数で全称量化する。最後に内部出力から要求型・要求効果への包含を課す。

未宣言の perform と handler の生成結果は偽制約になる。健全性の目標には Expr.Declared を明記した。これは計画の「整形式の入力」に必要な操作の作用域条件を具体化したものである。未宣言操作について偽制約の下で型付けを構成できるとは主張しない。unknownPerformNotTypable は、未宣言操作は任意の制約の下でも型付けできないことを証明する。

generationWF は生成制約の kind と束縛の整形式性を証明する。generationScope は、操作が宣言済みなら生成制約の自由項識別子が元の項の自由変数と一致することを証明する。`inferWF`・`inferScope`・`inferJudgmentWF` はこれらを環境付きの infer に拡張する。

`envLetInHolds` は環境付加の意味を実現可能性と解釈後の本体の充足へ分解する。`envInterpretLookup` は自由変数の右側優先と束縛添字の順序を保ち、`envLetInExists`・`envLetInForall` は型・効果の量化との交換を示す。`generationSubstitution`・`generationMonotone`・`generationValuePure` は完全性の代入・部分型・値の評価効果の分岐で必要な性質を証明する。

`generatedScheme` は右辺の生成スキームに環境を取り込む。`valueLetGeneration` はこのスキームを本体の環境に追加した推論との同値を示す。`generatedSchemeComparison` は右辺の局所的な帰納仮定からスキーム包含を導き、意味論の値の構文的表現可能性や完全性定理全体を仮定しない。`schemeExistsNonempty` と `valueLetCompletenessHolds` はスキーム包含に加えて生成スキームの実現可能性を証明する。`inferenceVariable`・`inferenceValueLet` と残る各分岐を `inferenceSoundnessAux` に統合し、全項の健全性を証明した。

## 7 証明済みの保証

progressGeneral は EffectFramework、型付け、空の項環境、kind を満たす割当て、および制約を実際に満たす割当てを前提とする。結論は、項が値であるか、一歩簡約できるか、解釈された評価効果に含まれる未処理操作を露出するかのいずれかである。

progressEffectSafety はこの結果を ProgressGoal に適用する。emptyEffectProgress は空効果と充足可能な制約の下で、現在の項が値または簡約可能であることを示す。preservationSteps と結合した effectSafety・emptyEffectSafety は、同じ保証を任意の到達状態に与える。

typingTypeEffectSubstitution は、型・効果代入を制約・スキーム・環境・結果型・効果に同時に適用して型付けを保つ。substBoundSemantics と entailsSubstBound は存在量化・全称量化を含む意味解釈と含意の保存を示す。型文脈のすべての kind が宣言済みという前提や、意味論の存在証人を型構文で表せるという前提は追加していない。

schemeValueSubstitution は SchemeValueSubstitutionGoal の正確な前提・結論を満たす。typingValueSubstitutionAux の帰納仮定は強い制約について一般化し、存在量化の内側で外側制約の shift と内側制約を合わせて代入する。RealizesScheme はこの帰納法で値の各具体化を扱う局所前提であり、generalizedValueRealizes で一般化導出から証明している。

betaPreservation、letPreservation、returnPreservation は、それぞれの簡約について型と効果の上界を保存する。let は単相・多相の両方を扱い、制約強化と存在量化を含む導出に適用できる。evalCtxReplacement は、すべての型文脈・制約・環境で成り立つ穴の型付け変換を、let 右辺を含む文脈全体へ持ち上げる。これらは閉項や具体モデルに限定した定理ではない。

operationClauseInstantiation は引数と継続の型を同じ型・効果引数で具体化する。ContextTyping の各補題は型文脈の拡張・制約強化・項束縛の追加の下で文脈を再構成し、resumeContextTyping・resumeTyping が継続の型付けを与える。exprOpenTwo・twoValueSubstitution は操作節の束縛順序 `[継続, 引数値]` を保つ。operationElimination は存在量化の作用域内で継続構成と代入を完了し、operationPreservation を導く。preservation は全簡約規則を統合し、preservationSteps は任意の Δ・C・Γ・型・効果上界を保つ。最終 Goal の追加前提や対象の限定は導入していない。

その他の主要な証明済み補題は、operationInstantiation、kindShift、evalKind、evalShift、valuePure、closedValueLambda、evalCtxShiftPlug、schemeUpperSet、generationWF、generationScope である。各補題の使用箇所と残る証明義務は ehmx-todo.md に記録する。

## 8 推論三定理

`Goals.lean` の Goal は命題の定義であり、それと同じ型の証明を別の宣言で与える。保存・安全性の Goal に加え、次の三定理を標準 `import EHMX` から公開する。

| 証明 | 元の命題 | 原典との対応 |
| --- | --- | --- |
| `inferenceSoundness` | `InferenceSoundnessGoal` | ATTAPL 10.4.4 の EHM(X) 拡張 |
| `inferenceCompleteness` | `InferenceCompletenessGoal` | ATTAPL 10.4.8 の EHM(X) 拡張 |
| `constraintGenerationPrincipality` | `PrincipalityGoal` | 429–430頁の主要制約性の EHM(X) 拡張 |

`inferenceSoundnessAux` は項の構造に帰納法を適用し、Δ・制約・環境・要求型・効果を一般化する。`inferenceExistsCase` により型・効果の存在変数を型付け導出の内部に保つ。操作宣言の自己具体化は `declarationOpenSelf`、全称操作節への移動は `entailsForallOpen` が担う。

`typingCompletenessHolds` は既存の `Typing` 導出に直接帰納法を適用する。割当てごとに外側制約と環境実現可能性を引き継ぐため、`strengthen` に不要な前提を追加しない。型・効果の評価値を存在証人として使い、`generationEvalCongruence` で生成側の束縛添字へ移す。handler の内部結果型・効果は保持し、任意の kind 適合引数列で操作節を検査する。値への `letMono` と多相 let も含む。

完全性の環境実現可能性条件は維持している。充足可能性・`ArrowSeparated`・意味論の値の構文的表現可能性は三定理の前提に追加していない。主要制約性は健全性と完全性から構成し、環境・項・要求型・効果を固定した制約の含意を保証する。ソルバーや最汎代入の存在は主張しない。

ソルバー、参照・ストア、組込み定数の簡約、複数操作節、shallow handler は対象外である。既存 HMX の証明や参照先リポジトリを変更していない。

## 9 型クラスを X とする固定モデル

`EHMX.TypeClasses` は HMX の `ClassEnv`・`InstanceRule`・整形式条件・アリティを共有する具体モデルである。型の意味値は Int・Bool・リスト・効果付き関数型・宣言アリティに従う追加構成子の木、効果の意味値は有限操作集合とする。関数型は引数に反変、結果型と潜在効果に共変とし、ほかの型木は同一の場合のみ比較する。宣言番号0は関数型頭部として維持するが、型構文では専用 `.arrow` を使い、`.other 0` は宣言しない。

`Member` はインスタンスとスーパークラス規則の最小閉包であり、クラスの非空性や所属判定器を前提にしない。関数型インスタンスの二つの型引数は入力型・結果型を参照し、潜在効果を検査しない。入れ子を含む効果付き型木を保持し、効果 kind 自体へのクラス制約は対象外とする。不正適用の全域化には Int を使い、`constructTag`・`constructArguments`・`constructorPreserves` が整形式な適用の名前と全引数を保存する。

`fixedFramework` と `fixedArrowSeparated` は任意の宣言データに対して証明済みである。`instanceEntailment` は `E.WF` と型引数の kind 0・潜在効果の kind 1 を要求し、`memberDeclared` は `E.WF` の下で所属先の宣言済み性を保証する。`memberEmbedIff` は空の潜在効果で埋め込んだ HMX 型木のクラス所属と元の所属の同値性を証明する。推論体系全体の同値性は主張しない。

同名前空間の `inferenceSoundness`・`inferenceCompleteness`・`constraintGenerationPrincipality` はモデル法則を内部で構成し、既存三定理を適用する。これは ATTAPL 10.4.4・10.4.8・429–430頁の EHM(X) 拡張の具体化であり、モデル構成そのものを原典の番号付き定理とは扱わない。操作シグネチャの整形式性、作用域、kind、完全性の環境実現可能性は元のまま維持する。

`TypeClassesRegression.lean` は Eq・Ord・Empty、条件付きリスト、空のクラス環境、追加構成子、任意の潜在効果を持つ関数型インスタンス、スーパークラス循環を検査する。資格付き `eq` の通常のスキームを用いる `λx.λy.eq x y` と、多相操作 `op : ∀β. β → β` を含む `eq (perform op x) y` の deep handler を直接型付けする。全称操作節では引数を継続へ渡し、処理後の効果は空である。両例に推論三定理を適用し、Int の割当てによる生成制約の充足可能性も証明する。

詳細と前提の対応は [型クラスモデル](typeclasses.md) を参照。辞書変換、メソッド本体や法則、インスタンス探索器、GHC 拡張、Haskell 全体との同値性、ソルバーの存在は対象外である。

## 10 再現と検証

lake build は HMX、EHMX、回帰例を検査する。回帰例は実行・生成・型付けを区別する。handlerGenerationWF は生成制約の整形式性であり、handler 全体の推論健全性ではない。SafetyRegression.lean は実際の型付けに最終保存定理を適用し、混合引数、let 右辺の捕捉、継続の二回利用、開いた環境、同じ操作・異なる操作の handler、操作節からの再実行を検査する。存在量化された型引数を使い、exists_ / strengthen / sub を経由する捕捉も含む。tests/EHMXGoals.lean は完成した九つの Goal と任意の Δ C Γ T ε に対する多歩保存の型を直接検査し、tests/EHMXAxioms.lean は全 EHMX 定理の依存公理を監査する。InferenceRegression.lean は開いた環境、遮蔽、束縛の複数段参照、充足不能な環境、値 let の局所的な健全性、混合 kind の操作と handler の生成補題を検査する。さらに InferenceTheoremRegression.lean は最終三定理を開いた環境・全項構成子・値への letMono・一つの let の異なる型と潜在効果での利用・充足不能な生成制約へ適用する。主要制約性から別の制約による含意も検査する。CI では tests/EHMXGoals.lean と tests/EHMXInference.lean も実行する。

仕様PDFは tools/build_ehmx_spec.py でこの文書から生成する。付録の構文・モデル前提・型付け・簡約・生成規則・最終目標の Lean 宣言はソースから直接取り込む。PDF内のコード表示に限り、Unicode 記号を ASCII 表記へ置換する。ソースのハッシュとPDFのハッシュを manifest に記録し、--check で古いPDFを検出する。PDF の作業は明示的な依頼があった場合のみ行い、Lean 証明の変更時の更新・整合性検査は必須としない。
