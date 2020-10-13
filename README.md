**Доверяй, но проверяй (trust, but verify)**

CVC4 is able to produce proofs for unsat results. The underlying deduction
rules are documented. This allows for independent verification of CVC4's
proofs. The deduction rules are specified in LFSC, the *Logical Framework with
Side Conditions*. Basically, this means that each proof rule is specified as a
function type in a dependently typed lambda calculus. Thus, proof verification
is type-checking. Type declarations can include side conditions, which are
functions written in a small functional language that supports a little bit of
mutability.

I'm wondering whether all of this means that CVC4's proof rules can relatively
easily be transliterated into Agda function types and CVC4 proofs into Agda
terms.

This repo is where I explore this idea a little, while learning Agda. I'm new
to dependent types, LFSC, and Agda. So, if there's an impossibility result that
I should be aware of, please do tell.

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

  * LFSC provides a way for side conditions to mark variables. A side condition
    can set and clear up to 32 different flags on a variable. That's the *little
    bit of mutability* mentioned above.

    This is used for performance optimizations: It allows us, for example, to
    go from "traverse a list of variables multiple times and remove a single
    variable each time" to "mark (in constant time) each variable to be removed
    and finally make a single pass over the list to remove all marked variables
    in one fell swoop".

    This is why variables aren't simply Agda's variables. Instead, there's a
    data type for variables, `Var` in `Env.agda`. Variables can thus be marked
    by placing them in an AVL set that represents a given flag.

  * Speaking of AVL. `AVL.agda` proves that you get out of an AVL tree what you
    stick in, i.e., that AVL tree lookups are correct with respect to AVL tree
    insertions.

  * The way in which I handle variables has implications on atoms. That's why
    my version of `decl_atom`, for example, differs from CVC4's. My approach
    requires an environment (of type `Env`) that maps `Var`s to `Formula`s,
    according to the `decl_atom`s in the proof. This is inconvenient, because I
    have to find all `decl_atom`s in a proof and create a matching environment.
    The proof rules then get parameterized by this environment, i.e., the `SAT`
    and `SMT` modules both take an `Env` parameter. When the created environment
    doesn't match the `decl_atom`s in the proof, then the proof won't
    type-check.

    I wonder whether I can do without this environment kludge. I basically need
    it to prove things like CVC4's `asf` and `ast` deduction rules. Right now,
    it seems to me that I cannot do without the environment. It seems to be a
    direct consequence of my choice to represent variables as data, i.e, as
    `Var`s, so I need a way to say what value a variable holds - which is the
    environment.

  * This is how to get from a `Formula` to an Agda type and a witness for it:

    * `eval` ascribes a truth value to a given `Formula`. It's based on `evalᵛ`,
      which does the same for `Var`s (by way of an environment).

    * The `Holds` data type says that a given `Formula` holds, i.e., that it
      `eval`uates to true.

    * `prop` is how the Agda type is made. It turns a `Holds` into a type.

    * `prove` turns a `Holds` into a witness value for the Agda type created by
      `prop`.

  * I extended `Formula`s a little. That's what the `boolˣ` and `equˣ` data
    constructors are. The idea is to use them to wrap sub-formulas. They don't
    change what the wrapped sub-formula `eval`uates to. They are only used to
    guide how `prop` and `prove` turn a `Formula` into an Agda type and a
    corresponding witness.

    An SMT solver "thinks" in terms of Booleans. So, as far as I can tell, when
    asking it to prove `A ⊎ B`, we actually need to ask it to prove `A ∨ B`.
    `boolˣ` and `equˣ` tell `prop` and `prove`, whether an `orᶠ` in a `Formula`
    should be translated to `⊎` or `∨`.

    Maybe there are better ways to do this. If so, let me know.

  * As all proofs are done via `eval`, which is based on Booleans, I don't seem
    to get into trouble with double negation. At least not yet. Again, let me
    know, if I should be aware of any impossibility results.

  * `Formula`s are a data type just like they are in LFSC proofs. I think that
    this would be called a deep embedding. In contrast, for terms, I'm trying to
    get away with a shallow embedding. It looks like I am able to do all proofs
    in `SAT.agda` and `SMT.agda` for any Agda type, as long as it is the carrier
    of a setoid.

    So far, this seems to work. But then again, Booleans are so far the only
    SMT theory (i.e., term sort) supported. What I'm a little skeptical about is
    is the `cong` deduction rule in CVC4's base theory in `Base.agda`. Looks
    like I'll need one or more `Π` records in `Cong.agda` for each supported SMT
    theory.

This is what a proof for `x = x` looks like when it's generated by CVC4.

```
unsat
(check
 ;; Declarations
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

I manually transliterated it to Agda - and it type-checks! See `Test.agda`.
The biggest difference lies in the handling of `decl_atom`. That's the
environment thing I pointed out above.

```
smt₁ =
  λ (x : Bool) →
  λ (as₁ : Holds trueᶠ) →
  λ (as₂ : Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x)))) →
  let let₁ = falseᶠ in
  mp (trust falseᶠ) λ pa₁ →
  mp (trust (notᶠ let₁)) λ pa₂ →
  let v₁ = var 1 in
  let a₁ = atom v₁ let₁ refl in
  mpᶜ (assum a₁ λ l₃ → clausi-f (contra l₃ pa₂)) λ pb₁ →
  mpᶜ (assum-¬ a₁ λ l₂ → clausi-f (contra pa₁ l₂)) λ pb₄ →
  mp⁺ (resolve-r⁺ pb₄ pb₁ v₁) id
```

Note how the above transliterated proof, `smt₁`, is used in `Test.agda` to prove
different propositions, depending on whether `boolˣ` and `equˣ` are inserted
into the `Formula`.

```
prop₁ : (x : Bool) → T x ⇔ T x
prop₁ x = final (iffᶠ (appᵇ x) (appᵇ x)) (smt₁ x (holds trueᶠ refl))

bool₁ : (x : Bool) → T (x ≡ᵇ x)
bool₁ x = final (boolˣ (iffᶠ (appᵇ x) (appᵇ x))) (smt₁ x (holds trueᶠ refl))

equ₁ : (x : Bool) → x ≡ x
equ₁ x = final (equˣ (appᵇ x) (appᵇ x)) (smt₁ x (holds trueᶠ refl))
```

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
