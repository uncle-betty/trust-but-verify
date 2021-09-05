*NOTE - I've abandoned this little experiment and it probably won't work
with more recent versions of Agda and/or the standard library. Also, please be
aware that CVC5 will come with a completely reworked proof infrastructure - I
don't know, how useful this repository will be going forward.*

**Доверяй, но проверяй (trust, but verify)**

CVC4 is able to produce proofs for `unsat` results. The underlying proof rules
are documented. This allows for independent verification of CVC4's proofs. The
proof rules are specified in LFSC, the *Logical Framework with Side
Conditions*. Basically, this means that each proof rule is specified as a
function type in a dependently typed lambda calculus. Thus, proof verification
is type-checking. Type declarations can include side conditions, which are
functions written in a small functional language that supports a little bit of
mutability.

I'm wondering whether all of this means that CVC4's proof rules can relatively
easily be transliterated to Agda function types and CVC4 proofs into Agda terms.

This repo is where I explore this idea a little, while learning Agda.

Currently, Boolean proofs are starting to work. I'd now like to start looking
into supporting my first theory, the theory of bit vectors, followed by the
theory of arrays.

Another thing I'd like to look into is performance. Parsing CVC4's proofs is
incredibly slow at this time. The really small test proofs in `Test.agda` take
over 8 minutes on my machine!

A few pointers:

  * LFSC is described in *SMT proof checking using a logical framework*:
    https://homepage.divms.uiowa.edu/~ajreynol/fmsd12.pdf

  * CVC4's current proof rules ("signatures") can be found in the CVC4
    repository: https://github.com/CVC4/CVC4/tree/master/proofs/signatures

Some things that might help you make sense of this repo:

  * Read the above paper.

  * The file names in this repo follow the naming conventions of CVC4's
    signatures; `smt.plf` becomes `SMT.agda`, etc. The structure of each file,
    i.e., the order of definitions, also mostly follows the signatures.

  * Definitions come with comments like `LFSC: clause_dedup`, which give the
    names of the corresponding declarations in CVC4's signatures.

  * My variables are a little different from LFSC's. In LFSC, each variable has
    a set of flags associated with it, which can be modified and tested in
    constant time. That's the *little bit of mutability* mentioned above.

    LFSC proofs use the flags to improve performance. For example, proofs may
    mark multiple variables, and then remove them all from a list with a single
    list traversal, i.e., in linear time.

    This is why I can't simply map LFSC variables to Agda's variables. Instead,
    I have a data type for variables, `Var` in `SAT.agda`. This allows me to put
    variables into AVL sets, for example. Indeed, a flag on a variable is set by
    placing the variable in an AVL set that represents that flag.

  * Speaking of AVL. `AVL.agda` proves that you get out of an AVL tree what you
    stick in, i.e., that AVL tree lookups are correct with respect to AVL tree
    insertions.

  * This is how to get from a `Formula` to an Agda type and a witness for it:

    * `eval` ascribes a truth value to a given `Formula`.

    * The `Holds` data type says that a given `Formula` holds, i.e., that it
      `eval`uates to true.

    * `prop` is how the Agda type is made. It turns a `Holds` into a type.

    * `prove` turns a `Holds` into a witness value for the Agda type created by
      `prop`.

    (I suspect that I reinvented the standard library's `Dec` data type.)

  * Formulas are represented by a data type just like they are in LFSC proofs.
    I think that this would be called a deep embedding. In contrast, for terms
    (theory atoms), I'm trying to get away with a shallow embedding.

    Instead of having a data type to represent, say, `x < y` for linear integer
    arithmetic and allowing such atoms to be plugged into formulas, I'm trying
    to generalize this to decidable propositions. I'd then have to show for each
    theory that its atoms are decidable.

`Test.agda` contains a simple proof of `x = x` for Boolean `x`. This is what
the proof generated by CVC4 looks like in LFSC. It's s-expressions, where `%` is
a lambda with a typed argument, `\` is a lambda with an untyped argument, `@`
is a let-binding, and `:` is type ascription. Everything else is a proof rule.

The general proof idea is to negate the proposition to be proved and, from
that, derive the empty clause, i.e., false. Each proof rule introduces a new
lemma in a new variable (`.PA248`, `.PA267`, ...) that helps us ultimately
get to false.

```
(check
(% x (term Bool)
(% A1 (th_holds true)
(% A0 (th_holds (not (iff (p_app x) (p_app x) )))
(: (holds cln)
(@ let1 false
(th_let_pf _ (trust_f false) (\ .PA248
(th_let_pf _ (trust_f (not let1)) (\ .PA267
(decl_atom let1 (\ .v1 (\ .a1
(satlem _ _ (ast _ _ _ .a1 (\ .l3 (clausify_false (contra _ .l3 .PA267)))) (\ .pb1
(satlem _ _ (asf _ _ _ .a1 (\ .l2 (clausify_false (contra _ .PA248 .l2)))) (\ .pb4
(satlem_simplify _ _ _ (R _ _ .pb4 .pb1 .v1) (\ empty empty)))))))))))))))))))
```

(I have no idea where the `(th_holds true)` comes from. Why does CVC4 want me
to provide a - trivial - proof that true holds?)

Submodule `SMT₁` contains a manually transliterated version of the proof. I have
different names for things, but other than that, it's pretty much 1:1.

```
module SMT₁ where
  proof : (x : Bool) → Holds trueᶠ → Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x))) → Holdsᶜ ε []
  proof =
    λ (x : Bool) →
    λ (as₁ : Holds trueᶠ) →
    λ (as₂ : Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x)))) →
    holdsᶜ-[]-ε $
    bind-let falseᶠ λ {
      let₁ reflₚ →
        mp (trust falseᶠ) λ pa₁ →
        mp (trust (notᶠ let₁)) λ pa₂ →
        bind-atom 1 let₁ ε λ {
          v₁ reflₚ env reflₚ a₁ →
            mpᶜ env (assum (a₁ env reflₚ) λ l₃ → clausi-f (contra l₃ pa₂)) λ pb₁ →
            mpᶜ env (assum-¬ (a₁ env reflₚ) λ l₂ → clausi-f (contra pa₁ l₂)) λ pb₄ →
            mp⁺ env (resolve-r⁺ env pb₄ pb₁ v₁) id
          }
      }
```

Submodule `SMT₂` illustrates how the automatic transliteration works.
`convertProof` parses the LFSC input and creates a type and a term of that type,
which are unquoted with `proofType` and `proofTerm`, respectively.

Lastly, the input file for CVC4 that produces the above LFSC proof looks like
this.

```
(set-logic QF_AUFBV)
(set-option :produce-proofs true)

(declare-const x Bool)
(assert (not (= x x)))

(check-sat)
(get-proof)
(exit)
```
