/-! Source prose and dependency diagrams. These strings are not hypotheses or proved results. -/
namespace HMX.SourceNotes
/-- main.pdf, printed p.34. -/
def domainEquation : String := "The domain V is the least solution of V = W_bottom + (V -> V) + sum_k (k V1 ... Varity(k))_bottom. Function values are continuous. The initial environment supplies names and types for predefined values."
/-- main.pdf, printed p.53. -/
def openWorld : String := "Trivial projections correspond to the open-world assumption: the range of possible instance types is not fixed in advance; a constraint with free variables cannot be ruled out merely from the currently known instances."
/-- main.pdf, printed p.58. -/
def comparisonExamples : String := "Sections 3.5.2--3.5.4 compare System O, Ohori and constrained-polymorphism extensions. These examples are not additional rules of the HMX logical system. Figure 3.3 is recorded separately."
/-- main.pdf, printed p.198. -/
def theorem8Proof : String := "The proof restricts to closed environments whose schemes are valid in Xt and Xc and additionally assumes projection closure. The statement of Theorem 8 does not list these restrictions."
/-- main.pdf, printed p.197. -/
def solvedComparison : String := "Please note, implicitly I assumed that all constraints appearing in a derivation C |-i sigma <= sigma-prime are in solved form. A similar reasoning as in the Transformation Theorem 7 could be applied to enforce this invariant."
/-- main.pdf, printed p.208. -/
def generalizationComponents : String := "The definition labels gen1 as the constraint component and gen2 as the scheme component; Lemmas 33--34 and 38--39 use the subscripts in the opposite order."
/-- main.pdf, printed p.16. -/
def figure23 : String := "Logical system, semantic model and inference system; Type Soundness connects logical typing with the model and Principal Types connects inference with logical typing."
/-- main.pdf, printed p.112. -/
def figure46 : String := "Inference W -> logical typing: Theorem 12. Logical -> normalized: Lemma 15. Normalized -> syntax-directed: Lemma 17. Syntax-directed -> W: Lemma 37. Completeness: Theorem 13. W <-> Wbyneed: principal constraint property and unitary unification."
/-- main.pdf, printed p.113. -/
def figure47 : String := "Constraint-form and term-form inference are connected through transformation and term reconstruction; Wterm <-> Wnormalize requires lifting. The numbered results are Theorems 7, 14, 15, 16, 17 and 18."
end HMX.SourceNotes
