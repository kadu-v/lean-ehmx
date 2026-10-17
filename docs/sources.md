# 出典と表現上の選択

## 参考PDF

PDFの内容は変更していません。ATTAPL が形式化の原典であり、FreezeML は証明経路、Sulzmann の博士論文は型クラス具体例の参考資料です。以下のPDFは第三者の著作物であり、本リポジトリの MIT ライセンスの対象外です。

| 資料 | 書誌情報 | 役割と参照ページ |
| --- | --- | --- |
| [ATTAPL 第10章](references/attapl-chapter10-the_essence_of_ml_type_inference.pdf) | François Pottier, Didier Rémy, “The Essence of ML Type Inference”, *Advanced Topics in Types and Programming Languages*, 第10章 | 原典。§10.1–10.5、印刷389–438頁＝PDF 1–50頁。PDF全体は144頁。§10.6以降は対象外 |
| [FreezeML](references/2207.09914v1.pdf) | Frank Emrich, Jan Stolarek, James Cheney, Sam Lindley, *Constraint-based type inference for FreezeML*, arXiv:2207.09914v1, 2022年7月20日 | 補助資料。PDF 13頁の定理1・2、27–32頁の補題9・11・12・15・18・19と付録A.2–A.3、42–43頁の付録C.1 |
| [Sulzmann 博士論文](references/sulzmann-2000-thesis.pdf) | Martin Sulzmann, *A General Framework for Hindley/Milner Type Systems with Constraints*, Yale University, 2000年5月 | 型クラスモデルの参考。§3.2（印刷28頁）、§3.2.1（32–33頁）、§3.5.2（56–58頁）。博士論文版の実装・証明はこのライブラリに含めない |

| ファイル | SHA-256 |
| --- | --- |
| `attapl-chapter10-the_essence_of_ml_type_inference.pdf` | `205dedec53c0015a902379ca5cf2eac578cec4b83c8cfad9809c18080baf6895` |
| `2207.09914v1.pdf` | `3885c022d3c171a8552150c33bf655657372416ac7730d9038bd90b2520fb815` |
| `sulzmann-2000-thesis.pdf` | `a76e1754b9ae8480257d0826c7a91c4ba885e9b8aba50441058a8405b7e31f5f` |

ATTAPL 423頁の固定モデルによる解釈を保ち、抽象的な X を等式制約に限定しません。FreezeML の「Soundness」は型付けから生成制約へ向かい、ATTAPL の完全性側に対応します。「Completeness」はその逆です。FreezeML の主要解、ソルバー、rigid/flexible 変数、単相性制約は仮定として移植していません。補題12のように充足だけから生の構文の WF を導くこともしていません。

## 転記の範囲

原典の番号付き71項目のうち、定義22・定理10・補題9・系1の42項目を Lean 宣言として収録しています。残る例15・演習12・注2は説明用で、必要な定義・主張のみを収録しています。演習全体の解答はありません。演習10.4.1は最初の主張のみで、末尾の閉じた環境での推論同値は形式化していません。

Figure 10-1–10-9、Figure 10-6の21個の同値則を定義・命題として収録しています。収録と証明は別です。定理・補題・系の対応と証明範囲は [proofs.md](proofs.md) にあります。以下は定義22件の対応です。「固有名なし」は原典が名称を付していないことを表します。

| 原典番号・正式名 | 印刷頁 | Lean 宣言 |
| --- | --- | --- |
| 10.1.14 / 固有名なし | 400 | [HMX.Signature](../HMX/Syntax.lean#L54)、[HMX.Signature.Valid](../HMX/Syntax.lean#L63) |
| 10.1.15 / 固有名なし | 401 | [HMX.TVar](../HMX/Syntax.lean#L11)、[HMX.Vars](../HMX/Syntax.lean#L12) |
| 10.1.16 / 固有名なし | 401 | [HMX.Ty](../HMX/Syntax.lean#L71)、[HMX.Ty.HasKind](../HMX/Syntax.lean#L81)、[HMX.Ty.fv](../HMX/Syntax.lean#L77) |
| 10.1.17 / 固有名なし | 401 | [HMX.Subst](../HMX/Syntax.lean#L87)、[HMX.Subst.dom](../HMX/Syntax.lean#L93)、[HMX.Subst.range](../HMX/Syntax.lean#L94)、[HMX.Subst.Valid](../HMX/Syntax.lean#L95)、[HMX.Subst.Idempotent](../HMX/Syntax.lean#L97)、[HMX.Ty.subst](../HMX/Syntax.lean#L89) |
| 10.1.18 / 固有名なし | 402 | [HMX.DMScheme](../HMX/Syntax.lean#L102)、[HMX.DMScheme.Instance](../HMX/Syntax.lean#L110) |
| 10.1.19 / 固有名なし | 402 | [HMX.DMEnv](../HMX/Syntax.lean#L191)、[HMX.lookup](../HMX/Syntax.lean#L193) |
| 10.2.1 / 固有名なし | 407 | [HMX.Signature](../HMX/Syntax.lean#L54)、[HMX.Predicate](../HMX/Syntax.lean#L113)、[HMX.Predicate.Kinds](../HMX/Syntax.lean#L155)、[HMX.Predicate.WF](../HMX/Syntax.lean#L159) |
| 10.2.2 / 固有名なし | 407 | [HMX.Constraint](../HMX/Syntax.lean#L120)、[HMX.Scheme](../HMX/Syntax.lean#L128)、[HMX.Constraint.WF](../HMX/Syntax.lean#L164)、[HMX.Scheme.WF](../HMX/Syntax.lean#L171)、[HMX.Constraint.fv](../HMX/Syntax.lean#L133)、[HMX.Constraint.fpi](../HMX/Syntax.lean#L145) |
| 10.2.3 / 固有名なし | 408 | [HMX.Scheme.instanceConstraint](../HMX/Syntax.lean#L182)、[HMX.Scheme.InstanceFresh](../HMX/Syntax.lean#L184)、[HMX.Scheme.exists_](../HMX/Syntax.lean#L179)、[HMX.Constraint.let_](../HMX/Syntax.lean#L187) |
| 10.2.4 / 固有名なし | 410 | [HMX.Env](../HMX/Syntax.lean#L190)、[HMX.Env.fpi](../HMX/Syntax.lean#L197)、[HMX.Env.dpi](../HMX/Syntax.lean#L198)、[HMX.Env.dfpi](../HMX/Syntax.lean#L199)、[HMX.Env.defIn](../HMX/Syntax.lean#L204)、[HMX.Env.letIn](../HMX/Syntax.lean#L207)、[HMX.Env.exists_](../HMX/Syntax.lean#L210) |
| 10.2.5 / 固有名なし | 411 | [HMX.Model](../HMX/Semantics.lean#L7)、[HMX.Model.Requirements](../HMX/Semantics.lean#L17) |
| 10.2.10 / 固有名なし | 413 | [HMX.Assignment](../HMX/Semantics.lean#L14)、[HMX.GroundEnv](../HMX/Semantics.lean#L15)、[HMX.Assignment.Valid](../HMX/Semantics.lean#L29)、[HMX.GroundEnv.Valid](../HMX/Semantics.lean#L32)、[HMX.Ty.eval](../HMX/Semantics.lean#L36)、[HMX.Constraint.Holds](../HMX/Semantics.lean#L52)、[HMX.Scheme.denote](../HMX/Semantics.lean#L61)、[HMX.Satisfiable](../HMX/Semantics.lean#L67) |
| 10.2.11 / 固有名なし | 415 | [HMX.Entails](../HMX/Semantics.lean#L70)、[HMX.Equivalent](../HMX/Semantics.lean#L73) |
| 10.2.14 / 固有名なし | 417 | [HMX.Determines](../HMX/Semantics.lean#L95) |
| 10.2.18 / 固有名なし | 421 | [HMX.SolvedForm](../HMX/SolvedForms.lean#L33) |
| 10.2.20 / 固有名なし | 421 | [HMX.CanonicalSolvedForm](../HMX/SolvedForms.lean#L38) |
| 10.2.22 / 固有名なし | 422 | [HMX.Subst.Closure](../HMX/SolvedForms.lean#L43)、[HMX.MostGeneralUnifier](../HMX/SolvedForms.lean#L48) |
| 10.5.2 / 固有名なし | 434 | [HMX.InitialEnvironment](../HMX/Safety.lean#L14) |
| 10.5.3 / 固有名なし | 435 | [HMX.ReferenceConstructor](../HMX/Safety.lean#L19)、[HMX.StoreType](../HMX/Safety.lean#L24)、[HMX.StoreType.WF](../HMX/Safety.lean#L27)、[HMX.StoreType.refEnv](../HMX/Safety.lean#L32)、[HMX.generateStore](../HMX/Safety.lean#L36)、[HMX.generateConfig](../HMX/Safety.lean#L41)、[HMX.Config.WellTyped](../HMX/Safety.lean#L47) |
| 10.5.4 / 固有名なし | 436 | [HMX.Config.Approximates](../HMX/Safety.lean#L53) |
| 10.5.5 / 固有名なし | 436 | [HMX.ConstantsAdequate](../HMX/Safety.lean#L82) |
| 10.5.6 / 固有名なし | 437 | [HMX.ValueRestricted](../HMX/Operational.lean#L92)、[HMX.Config.ValueRestricted](../HMX/Operational.lean#L99)、[HMX.SafetyMode](../HMX/Safety.lean#L63)、[HMX.SafetyMode.Admitted](../HMX/Safety.lean#L68)、[HMX.SafetyMode.Requirement](../HMX/Safety.lean#L78) |

## 曖昧さ・読み・未解決事項

以下は従来の記録の識別子を保持したものです。原典の誤記候補を修正せず、未定義記号を型付き引数にする方針を保っています。表現の選択と原典への反例を混同しません。

- **A-01 / 10.3.7、428頁**：翻訳 `J·Kθ` の構成が省略されています。`HMX.DMTranslation` は型付き引数で、`TranslationDomain` と `DMTranslation.Meaning` が定義域と意図を記録します。任意の翻訳に対して定理が成り立つという主張ではなく、翻訳の存在・正当性は未証明です。
- **A-02 / 10.1.19・10.5.2、435頁**：環境は有限列ですが定数集合 Q は無限でもよく、初期環境の定義域を Q とする条件との関係は未解決です。Q の有限性を追加していません。
- **A-03 / 10.2.17、420頁**：文脈の構文は穴0個を許します。let文脈への制限と原文の命題を保持し、穴が非空という条件は追加していません。固定された真の文脈が適用範囲の問題を示します。命題の修正・証明はありません。
- **A-04 / 10.4.4、433頁**：原文には `t.fpi ⊆ Γ.dpi` が明記されていません。HM(X)の判断は制約に自由なプログラム識別子がないことを要求するため、未束縛識別子の生成制約は `JudgmentWF` の外に出ます。原文の適用範囲は未解決です。
- **A-05 / 10.5.6・10.5.8・10.5.11、437頁**：値制限は `SafetyMode.valueRestricted` で構成・δの両端・簡約経路・停止状態に共通の制限を課します。純粋な場合は `PureSemantics` を要求します。原文の非形式的な構文制限との同値は未証明です。
- **A-06 / 10.1.14–10.1.16、401頁**：生の帰納的構文に `WF` / `HasKind` を付け、可算な名前を自然数、引数を順序付き有限列で表します。kindを満たさない生の値を原典の型とは扱いません。
- **A-07 / 10.2.10、414頁**：基底環境の欠けた束縛は空の上方閉集合として表します。観測はインスタンス化の所属のみですが、`Option` による部分写像との同値は未証明です。
- **A-08 / 10.2.14、417頁**：`Determines` の量化は原文の構文的環境 Γ を保ち、`def Γ in C` の充足に必要な基底環境を別に明記します。Γ を基底環境へ読み替えていません。
- **A-09 / 10.2.18・10.2.20・10.2.22、422頁**：代入の定義域は実際に非恒等となる変数の集合です。閉鎖はこの集合を列挙します。一般の代入に冪等性を要求せず、解形式の左辺変数と存在束縛の重なりを許します。
- **A-10 / 10.1.19、394頁**：ストアとストア型は一意なキーの有限連想列です。有限写像としての等しさ・項のα変換を代表元の変換規則で明示します。操作的意味論全体と原典の商構文の同値は未証明です。
- **A-11 / 演習10.4.1、430頁**：最初の主張のみを形式化し、最後の閉じた環境での推論同値は未形式化です。
- **A-12 / 10.1.17・10.2.22、401頁、解決済みの転記修正**：`Subst.Valid` は実際の代入定義域の変数に宣言済みkindを要求します。生の `TVar` に含まれる未宣言kindへの変更を原典の変数として数えないための既存の修正です。今回の整理では定義を変更していません。
- **A-13 / 10.2.10・10.3.4・10.4.4・10.4.8**：`HMX.LN` は証明用の別表現です。項・型の添字を分離し、同時束縛の順序変更を `BinderEq` で明示します。WF・自由変数・α同値・意味論・Framework・制約生成・型付けの対応と名前付き推論への移送は証明済みです。任意のLN構文が名前付き符号化の像とは限らず、[CorrespondenceRegression.lean](../HMX/LocallyNameless/Proofs/CorrespondenceRegression.lean) に定数遮蔽の反例と新鮮変数による意味保存例があります。これは構文的な逆変換の仮定への反例で、原典の型付け定理への反例ではありません。型付け対応は環境実現可能性や推論定理を仮定しません。
- **A-14 / 10.4.4、433頁**：原文を保持したまま、別の `_scoped` 命題を証明しています。名前付きの作用域条件付き健全性・主要性と、既存の実現可能性条件を保った完全性は証明済みです。これによりA-04が解決したとは扱いません。
- **A-TC-01 / 423頁と博士論文の参照箇所**：型クラスは新しい固定モデルの構成です。有限の閉じた型木と最小の帰納的所属を用います。空クラスの存在制約は充足不能で、開世界の存在法則は追加しません。選択したモデルの性質であり、原典への反例ではありません。詳細は [typeclasses.md](typeclasses.md) を参照してください。
