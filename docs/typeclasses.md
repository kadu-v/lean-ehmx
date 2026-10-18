# HMX と EHM(X) の型クラス固定モデル

以下の既存 HMX モデルと、後半の EHM(X) モデルを区別します。どちらも博論の定理の転記ではなく、ATTAPLの既存定義を満たす具体的なXの構成です。定義と命題は [HMX/TypeClasses.lean](../HMX/TypeClasses.lean)、証明は [TypeClasses.lean](../HMX/LocallyNameless/Proofs/TypeClasses.lean)、具体例は [TypeClassesRegression.lean](../HMX/LocallyNameless/Proofs/TypeClassesRegression.lean) にあります。制約推論・表現対応51件とは別に、構成・適用10件を証明しています（[証明範囲](proofs.md)）。

## 原典との対応

| 資料 | 参照箇所 | 採用した内容 |
|---|---|---|
| Sulzmann, [博士論文](references/sulzmann-2000-thesis.pdf) | §3.2、印刷28頁、§3.2.1、印刷32–33頁 | 型言語・制約・初期環境を分け、プリミティブを初期環境に置く |
| 同上 | §3.5.2、印刷56–58頁 | 単一引数のクラス制約、`Eq α`、`eq`、`λx.λy.eq x y`、閉世界での存在量化 |
| ATTAPL、[第10章PDF](references/attapl-chapter10-the_essence_of_ml_type_inference.pdf) | 印刷423頁 | 制約を一つの固定モデルで解釈する |
| 同上 | 10.4.4 Soundness、10.4.8 Completeness、印刷429–430頁の主要制約性 | 既証明の名前付き版をこのモデルに適用する |

有限の閉じた型木、クラス宣言のデータ形式、スーパークラスとインスタンスからの最小帰納的所属関係、例のインスタンス集合はこのモデル独自の構成です。原典にこの構成や番号付き定理が記載されているとは扱いません。博論の制約の充足可能性規約をATTAPLの型付け規則へ追加しません。推論の健全性は型安全性やメソッドの実装の正しさを意味しません。

## 固定モデルの構成

normal kindのみを用います。コンストラクタ名は `0 = arrow`、`1 = Int`、`2 = Bool`、`3 = list` とし、追加名 `4 + i` のアリティを `extraArities[i]` に記録します。追加宣言は有限列ですが、各アリティは任意の自然数です。これは具体例の宣言形式の選択であり、原典の抽象定理に有限性の仮定を追加するものではありません。

`Ground` は型変数を持たない帰納的な型木です。追加コンストラクタの子はアリティに応じた `Fin n → Ground` であり、引数数の不一致を持つ木は作れません。意味論の全域関数 `construct` は未宣言名・不正な引数数に `Int` を返しますが、`HasKind` を満たす型ではこの補完分岐を使いません。`constructTag` と `constructArguments` が有効な適用で名前と全引数を保存することを証明し、`constructInjective` が自由な構成子としての単射性を証明します。

`ClassEnv` はクラス名の集合、スーパークラス辺 `(子クラス, 親クラス)`、インスタンス規則を持ちます。規則の各前提 `(c,i)` は頭部 `F a₀ … aₙ₋₁` の第 `i` 引数へのクラス制約です。`ClassEnv.WF` は宣言されたクラス名、コンストラクタ名、引数参照の範囲を確認します。`Member` はこれらの規則による最小閉包です。循環したスーパークラスだけで所属が生まれることはありません。

`Framework` はすべての宣言データに対して成立します。クラスの解釈自体にはATTAPL側の追加公理がなく、空の所属関係も許すためです。宣言規則として使用する際は `ClassEnv.WF` を確認し、`memberDeclared` で所属先が宣言されたクラスであることを保証します。条件付きインスタンスの含意は `WF` を明示的に要求します。モデル成立やクラス非空性を仮定するデータフィールドはありません。

部分型関係は型木の等しさです。関数型の単射性から `ArrowLaw`、異なるコンストラクタの分離から全宣言名を対象とする `Isolation` を導きます。`classAtom c T` は既存の `.atom (.other c) [T]` です。`instanceContext` は規則の前提の連言（前提なしなら真）です。メソッドは既存の資格付き `Scheme` として項環境に置きます。

## 定理の適用と回帰例

`namedSoundness`、`namedCompleteness`、`namedPrincipality` の証明は構成済みの `Framework` を使います。呼出側にはFrameworkの証明を要求せず、健全性・主要性の作用域条件と完全性の環境実現可能性条件をそのまま保持します。

例では `Eq = 0`、`Ord = 1`、`Empty = 2`、`Ord → Eq` とし、Eq・OrdそれぞれにInt・Boolの基底インスタンスとリストの条件付きインスタンスを与えます。`Ord α ⊨ Eq α`、`Eq α ⊨ Eq [α]`、入れ子リストの所属を証明します。関数型のEq所属がないことは、スーパークラスの導出も含めて反転して証明します。

`eq : ∀α[Eq α]. α → α → Bool` を定数0として `initialEnv` に登録し、`Eq α` のもとで `λx.λy.eq x y` を名前付き規則から型付けします。生成制約について健全性・完全性・主要制約性を適用し、具体的なIntの割当てからその充足可能性も証明します。

Emptyはインスタンスも入ってくるスーパークラス辺も持ちません。この固定モデルでは `∃α. Empty α` は充足不能で、真と同値ではありません。これは選択したモデルの性質であり、博論の開世界の定理への反例ではありません。開世界の `∃α. Eq α ≡ true` をモデルの規則として追加していません。

このほか、クラス制約の連言・存在量化、関数型のEq制約の充足不能性、空のクラス環境、アリティ0・3の追加コンストラクタを検査します。探索器、辞書変換、メソッド法則、GHC拡張、Haskell全体との同値性は対象外です。参考資料の書誌情報とハッシュは [sources.md](sources.md) にあります。

## EHM(X) の固定モデル

定義は [EHMX/TypeClasses.lean](../EHMX/TypeClasses.lean)、証明は [EHMX/Proofs/TypeClasses.lean](../EHMX/Proofs/TypeClasses.lean)、回帰は [EHMX/TypeClassesRegression.lean](../EHMX/TypeClassesRegression.lean) にあり、すべて標準 `import EHMX` から利用できます。以下の名前は `EHMX.TypeClasses` 内です。モデル構成そのものは新しい X の実例であり、原典の番号付き定理の転記ではありません。推論保証は ATTAPL 10.4.4・10.4.8・429–430頁の EHM(X) 拡張を適用します。

| 項目 | HMX | EHM(X) |
| --- | --- | --- |
| 宣言データ | `ClassEnv`、`InstanceRule`、`arity`、各 `WF` | HMX の同じ定義を再利用 |
| 型と効果の値 | 型木のみ | `Ground.type` と有限集合の `Ground.effect`、kind 0 と 1 |
| 関数型 | 入力型・結果型 | 入力型・潜在効果・結果型。入れ子の効果も保持 |
| 型順序 | 等式 | 関数型の引数に反変、結果と潜在効果に共変。ほかの型木は同一の場合のみ比較 |
| 構成子番号 | 0 が関数型 | 宣言の番号0は維持し、型構文では専用 `.arrow` に変換。`.other 0` は未宣言 |
| クラス制約 | 型への単一引数述語 | 型への単一引数述語。効果 kind 自体への制約は扱わない |

`GroundType` の追加構成子の引数は `Fin n → GroundType` であり、宣言アリティを型で保証します。`construct` と `constructor` は不正な適用を Int で補完します。`constructTag`・`constructArguments` と `constructorPreserves` は、宣言済みの正しいアリティを持つ型引数列について、構成子名と全引数を保存することを証明します。回帰ではアリティ0・3、効果値を誤って型引数に渡す場合、入れ子の関数型の潜在効果を保持する場合も検査します。

`Member` は完全な効果付き型木を引数に取る最小帰納関係です。関数型頭部のインスタンスは入力型と結果型に条件を課し、潜在効果は任意です。所属の定義で型木から効果を消してはいません。スーパークラスの循環は許しますが、循環だけでは所属が生成されないことも回帰で証明しています。

`groundRefl`・`groundTrans`・`groundAntisymm`、構成子の kind 保存、効果集合の法則、関数型の順序法則から `fixedFramework E : EffectFramework (signature E) (model E)` を証明しました。これは任意の `ClassEnv` について成立し、`E.WF` やクラスの非空性を要求しません。`fixedArrowSeparated` は通常の型構成子と関数型を分離します。

`classAtomMeaning` はクラス制約の充足を、型の評価値と `Member` の関係として記述します。`superclassEntailment` と `instanceEntailment` は宣言規則を制約の含意へ接続します。後者は `E.WF`、型引数の kind 0、関数型頭部の潜在効果の kind 1 を明示します。`memberDeclared` は `E.WF` の下で所属先クラスが宣言済みであることを保証します。

`embed` は HMX 型木のすべての関数型に空の潜在効果を入れます。構成子を保存する `embedConstruct`・`eraseConstruct` と、所属導出に対する `memberEmbed`・`memberErase` により、`memberEmbedIff` がこの埋込み上の所属の同値性を証明します。これは推論体系全体の翻訳・同値性を主張するものではありません。

`inferenceSoundness`・`inferenceCompleteness`・`constraintGenerationPrincipality` は既存の三定理の特殊化です。呼出側は操作シグネチャの整形式性と元の定理の条件を与えます。モデル法則は内部で構成し、独立した推論の帰納法や追加前提は導入していません。

## EHM(X) の型付けと生成制約の回帰

`Regression.exampleEnv` は HMX と同じ Eq・Ord・Empty、`Ord → Eq`、Int・Bool・条件付きリストの宣言を持ちます。入れ子リストの所属、関数型の Eq 所属がないこと、Empty の存在制約の充足不能性を証明します。これらの否定例は選択した固定モデルの性質です。別の `arrowEnv` では条件付き関数型インスタンスを宣言し、任意の潜在効果に対する所属と含意を検査します。

`eqScheme` は通常のスキーム `∀α[Eq α]. α →∅ α →∅ Bool` です。`initialEnv` の自由識別子0にこのスキームを置き、`eqLambdaTyping` が `Eq α` の下で `λx.λy.eq x y` を直接型付けします。

`handledMethodTyping` は、外側に同じ型 α の x・y を持つ環境で `eq (perform op x) y` を deep handler で処理する導出です。操作宣言は `op : ∀β. β → β`、return 節は恒等、操作節は引数を継続へ渡します。`universalClauseTyping` は任意の β の下で、外側の Eq 制約・環境を shift したままこの節を型付けし、処理後の効果は空になります。

両方の直接導出に対して、`eqLambdaInferenceSoundness`・`eqLambdaInferenceCompleteness`・`eqLambdaPrincipalConstraint` と、対応する `handledMethod...` を証明しています。`eqLambdaGeneratedSatisfiable`・`handledMethodGeneratedSatisfiable` は具体的な Int の割当てから生成制約の充足可能性を示します。標準 import からの公開入口も `tests/EHMXInference.lean` の `example` で適用検査しています。

この範囲の証明義務は完了しています。辞書変換、メソッド本体の実行意味や法則、インスタンス探索器、GHC 拡張、Haskell 全体との同値性、ソルバーの存在は対象外です。
