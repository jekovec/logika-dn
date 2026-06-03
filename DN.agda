module DN where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)



-- 1. --
-- Propositional logic formulas: variables (indexed by ℕ), negation, conjunction, disjunction
data Formula : Set where
  Var : ℕ → Formula
  ¬_  : Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula

-- 2. --
-- A literal is either a positive variable (Var n) or a negated variable (¬ n)
data Literal : Set where
  Var : ℕ → Literal
  ¬_  : ℕ → Literal

-- NNF (Negation Normal Form): negations are pushed all the way down to literals
data NNF : Set where
  Lit : Literal → NNF
  _∧_ : NNF → NNF → NNF
  _∨_ : NNF → NNF → NNF


-- 3. --
-- Mutually recursive conversion to NNF.
-- to-nnf handles the positive case; to-nnf-neg handles the case where the
-- formula is under a negation, applying De Morgan's laws as it goes.
mutual
    to-nnf : Formula → NNF
    to-nnf (Var f) = Lit (Var f)
    to-nnf (f ∧ g) = to-nnf f ∧ to-nnf g
    to-nnf (f ∨ g) = to-nnf f ∨ to-nnf g
    to-nnf (¬ f) = to-nnf-neg f      -- enter negated mode

    -- Converts a formula that is under a negation into NNF.
    -- ¬(f ∧ g) → ¬f ∨ ¬g   (De Morgan)
    -- ¬(f ∨ g) → ¬f ∧ ¬g   (De Morgan)
    -- ¬¬f      → f           (double negation elimination)
    to-nnf-neg : Formula → NNF
    to-nnf-neg (Var f) = Lit (¬ f)
    to-nnf-neg (f ∧ g) = to-nnf-neg f ∨ to-nnf-neg g
    to-nnf-neg (f ∨ g) = to-nnf-neg f ∧ to-nnf-neg g
    to-nnf-neg (¬ f) = to-nnf f

-- ¬(p ∧ q) becomes ¬p ∨ ¬q
_ : to-nnf (¬ (Var 0 ∧ Var 1)) ≡ Lit (¬ 0) ∨ Lit (¬ 1)
_ = refl

-- ¬¬p becomes p
_ : to-nnf (¬ ¬ Var 0) ≡ Lit (Var 0)
_ = refl

-- ¬(p ∨ q) becomes ¬p ∧ ¬q
_ : to-nnf (¬ (Var 0 ∨ Var 1)) ≡ Lit (¬ 0) ∧ Lit (¬ 1)
_ = refl
-- 4. --

-- Decidability: for any proposition A, either we have a proof of A (yes),
-- or a proof that A leads to contradiction (no).
data Dec (A : Set) : Set where
  yes : A       → Dec A
  no  : (A → ⊥) → Dec A

-- A "decidable type": bundles a carrier set with a decision procedure for
-- propositional equality. This lets us test whether two values are equal.
record DecType : Set₁ where
  field
    carr   : Set                              -- the underlying type
    test-≡ : (x y : carr) → Dec (x ≡ y)      -- equality test returning Dec

open DecType

-- DecType instance for natural numbers.
𝒩 : DecType
𝒩 .carr = ℕ
𝒩 .test-≡ zero    zero    = yes refl
𝒩 .test-≡ zero    (suc n) = no (λ ())         
𝒩 .test-≡ (suc m) zero    = no (λ ())         
𝒩 .test-≡ (suc m) (suc n) with 𝒩 .test-≡ m n
... | yes refl = yes refl                     
... | no  m≢n  = no (λ { refl → m≢n refl }) 

-- Parameterised module for association lists (finite maps) with key type K and value type V.
-- The invariant NoDupKeys ensures every key appears at most once.
module AssocModule (K : DecType) (V : Set) where

  -- Proof-relevant membership: k ∈ kvs witnesses that key k appears in the list.
  -- ∈-here  : k is the head of the list.
  -- ∈-there : k appears somewhere in the tail.
  data _∈_ : carr K → List (carr K × V) → Set where
    ∈-here  : {k : carr K} {v : V} {kvs : List (carr K × V)}
            → k ∈ ((k , v) ∷ kvs)
    ∈-there : {k k' : carr K} {v : V} {kvs : List (carr K × V)}
            → k ∈ kvs → k ∈ ((k' , v) ∷ kvs)

  -- Predicate asserting that all keys in the list are distinct.
  -- ndk-[] : the empty list trivially has no duplicates.
  -- ndk-∷  : prepend (k,v) only if k is not already in the tail,
  --          and the tail itself has no duplicate keys.
  data NoDupKeys : List (carr K × V) → Set where
    ndk-[]  : NoDupKeys []
    ndk-∷   : {k : carr K} {v : V} {kvs : List (carr K × V)}
            → (k ∈ kvs → ⊥)        -- k does not appear in the rest
            → NoDupKeys kvs
            → NoDupKeys ((k , v) ∷ kvs)

  -- An association list: a list of key-value pairs together with a proof
  -- that all keys are unique.
  record Assoc : Set where
    constructor mkAssoc
    field
      list  : List (carr K × V)
      nodup : NoDupKeys list

  open Assoc

  -- The empty map.
  empty : Assoc
  empty = mkAssoc [] ndk-[]

  -- Extract the value associated with a key, given a membership proof.
  -- Since ∈-here carries the value in its implicit argument, we just read it off.
  lookup : {k : carr K} {kvs : List (carr K × V)} → k ∈ kvs → V
  lookup (∈-here {v = v}) = v
  lookup (∈-there p)      = lookup p

  -- Decidable membership test: either produce a proof that k ∈ kvs, or
  -- a proof that no such membership exists.
  -- Base case: empty list, trivially no.
  -- Inductive case: check if k ≡ k' (the head key).
  --   yes: k is here.
  --   no:  recurse into the tail; wrap a found proof with ∈-there,
  --        or combine both refutations to rule out membership entirely.
  _∈?_ : (k : carr K) → (kvs : List (carr K × V)) → Dec (k ∈ kvs)
  k ∈? [] = no (λ ())
  k ∈? ((k' , v) ∷ kvs) with K .test-≡ k k'
  ... | yes refl = yes ∈-here
  ... | no neq   with k ∈? kvs
  ...   | yes p    = yes (∈-there p)
  ...   | no notIn = no (λ { ∈-here → neq refl ; (∈-there q) → notIn q })

  -- Lookup by key, returning Maybe V.
  -- Uses ∈? to decide membership; on success, follows the proof to get the value.
  _‼_ : Assoc → carr K → Maybe V
  a ‼ k with k ∈? (a .list)
  ... | yes p = just (lookup p)
  ... | no _  = nothing

  -- Insert or update a key-value pair in a raw list (without the NoDupKeys invariant).
  -- If the list is empty, create a singleton.
  -- If the head key matches, replace it.
  -- Otherwise, keep the head and recurse into the tail.
  raw-update : List (carr K × V) → carr K → V → List (carr K × V)
  raw-update [] k v = (k , v) ∷ []
  raw-update ((k' , v') ∷ kvs) k v with K .test-≡ k k'
  ... | yes refl = (k , v) ∷ kvs      -- replace existing entry
  ... | no _     = (k' , v') ∷ raw-update kvs k v   -- keep head, recurse

  -- Lemma: if x ∈ raw-update kvs y v and x ≠ y, then x was already in kvs.
  -- This is needed to prove that raw-update preserves NoDupKeys.
  -- Cases:
  --   empty list: x ∈ [y,v] and x ≠ y is a contradiction (only member is y).
  --   head k'' ≡ y: the updated head is y; if x is there, x ≠ y → contradiction;
  --                 if x is in the tail, it was already in the tail.
  --   head k'' ≠ y: if x is the head, it was already there; otherwise recurse into tail.
  update-∈ : (kvs : List (carr K × V)) (x y : carr K) (v : V)
           → (x ≡ y → ⊥) → x ∈ raw-update kvs y v → x ∈ kvs
  update-∈ [] x y v x≠y ∈-here       = ⊥-elim (x≠y refl)
  update-∈ [] x y v x≠y (∈-there ())
  update-∈ ((k'' , v'') ∷ kvs) x y v x≠y mem with K .test-≡ y k''
  ... | yes refl with mem
  ...   | ∈-here    = ⊥-elim (x≠y refl)
  ...   | ∈-there p = ∈-there p
  update-∈ ((k'' , v'') ∷ kvs) x y v x≠y mem | no _ with mem
  ...   | ∈-here    = ∈-here
  ...   | ∈-there p = ∈-there (update-∈ kvs x y v x≠y p)

  -- Proof that raw-update preserves the NoDupKeys invariant.
  -- If we update key k in a duplicate-free list, the result is still duplicate-free.
  -- Base case: inserting into [] gives a singleton, which trivially has no duplicates.
  -- Inductive case (head key k' ≡ k): we replace the head; the tail is unchanged,
  --   so the same "notIn" proof still applies.
  -- Inductive case (head key k' ≠ k): we recurse into the tail. The new head k'
  --   must not appear in the updated tail — we use update-∈ to show that any
  --   membership in the updated tail implies membership in the original tail,
  --   contradicting notIn. The tail's own NoDupKeys follows by induction.
  update-nodup : (kvs : List (carr K × V)) → NoDupKeys kvs
               → (k : carr K) → (v : V) → NoDupKeys (raw-update kvs k v)
  update-nodup [] ndk-[] k v = ndk-∷ (λ ()) ndk-[]
  update-nodup ((k' , v') ∷ kvs) (ndk-∷ notIn nd) k v with K .test-≡ k k'
  ... | yes refl = ndk-∷ notIn nd
  ... | no q     = ndk-∷ (λ mem → notIn (update-∈ kvs k' k v (λ eq → q (sym eq)) mem))
                         (update-nodup kvs nd k v)

  -- The safe update operation on Assoc: insert or overwrite a key-value pair
  -- while maintaining the NoDupKeys invariant via update-nodup.
  _[_]≔_ : Assoc → carr K → V → Assoc
  a [ k ]≔ v = mkAssoc (raw-update (a .list) k v)
                       (update-nodup (a .list) (a .nodup) k v)

-- Instantiate AssocModule with natural number keys and Bool values.
-- This gives us a variable assignment: a finite map from variable indices to truth values.
open AssocModule 𝒩 Bool

Assignment : Set
Assignment = Assoc

myMap : Assignment
myMap = ((empty [ 0 ]≔ true) [ 1 ]≔ false) [ 2 ]≔ true

_ : myMap ‼ 1 ≡ just false
_ = refl

_ : myMap ‼ 99 ≡ nothing    -- key not present
_ = refl

myMap2 : Assignment
myMap2 = myMap [ 0 ]≔ false   -- overwrite key 0

_ : myMap2 ‼ 0 ≡ just false
_ = refl

-- 5. --

-- Some helpers
not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

_||_ : Bool → Bool → Bool
true  || _ = true
false || b = b

-- Evaluate a formula under an assignment.

eval : Assignment → Formula → Maybe Bool
eval a (Var x) = a ‼ x

eval a (¬ f) with eval a f
... | just b  = just (not b)
... | nothing = nothing

eval a (f ∧ g) with eval a f | eval a g
... | just b₁ | just b₂ = just (b₁ && b₂)
... | _       | _       = nothing

eval a (f ∨ g) with eval a f | eval a g
... | just b₁ | just b₂ = just (b₁ || b₂)
... | _       | _       = nothing


-- 6. --

-- Lieteral helper

eval-lit : Assignment → Literal → Maybe Bool
eval-lit a (Var x) with a ‼ x
... | just true  = just true
... | just false = just false
... | nothing    = nothing

eval-lit a (¬ x) with a ‼ x
... | just true  = just false
... | just false = just true
... | nothing    = nothing


-- Evaluate NNF formula

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf a (Lit l) = eval-lit a l

eval-nnf a (f ∧ g) with eval-nnf a f | eval-nnf a g
... | just b₁ | just b₂ = just (b₁ && b₂)
... | _       | _       = nothing

eval-nnf a (f ∨ g) with eval-nnf a f | eval-nnf a g
... | just b₁ | just b₂ = just (b₁ || b₂)
... | _       | _       = nothing


-- 7. --
-- Literal already defined

data Disjunct : Set where
  Lit : Literal → Disjunct
  _∨_ : Literal → Disjunct → Disjunct

data CNF : Set where
  Disj : Disjunct → CNF
  _∧_ : Disjunct → CNF → CNF
  Empty : CNF


-- 8. --

-- Disjunction helper

eval-disj : Assignment → Disjunct → Maybe Bool
eval-disj a (Lit l)  = eval-lit a l

eval-disj a (f ∨ g) with eval-lit a f | eval-disj a g
... | just b₁ | just b₂ = just (b₁ || b₂)
... | _       | _       = nothing


-- Evaluate CNF formula

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf a Empty    = just true
eval-cnf a (Disj f) = eval-disj a f

eval-cnf a (f ∧ g) with eval-disj a f | eval-cnf a g
... | just b₁ | just b₂ = just (b₁ && b₂)
... | _       | _       = nothing

-- 9. --

-- for dpll we need representation that can handle empty clauses

Clause : Set
Clause = List Literal

FormulaS : Set
FormulaS = List Clause

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

_==ℕ_ : ℕ → ℕ → Bool
m ==ℕ n with 𝒩 .test-≡ m n
... | yes _ = true
... | no  _ = false

lit-var : Literal → ℕ
lit-var (Var x) = x
lit-var (¬ x)   = x

lit-sign : Literal → Bool
lit-sign (Var _) = true
lit-sign (¬ _)   = false

negate-lit : Literal → Literal
negate-lit (Var x) = ¬ x
negate-lit (¬ x)   = Var x

-- convert cnf into rep for dpll

disj→clause : Disjunct → Clause
disj→clause (Lit l) = l ∷ []
disj→clause (l ∨ d) = l ∷ disj→clause d

cnf→formula : CNF → FormulaS
cnf→formula (Disj d) = disj→clause d ∷ []
cnf→formula (d ∧ f)  = disj→clause d ∷ cnf→formula f
cnf→formula Empty = []

-- literal membership

lit-eq : Literal → Literal → Bool
lit-eq (Var x) (Var y) = x ==ℕ y
lit-eq (¬ x)   (¬ y)   = x ==ℕ y
lit-eq _       _       = false

contains-lit : Literal → Clause → Bool
contains-lit l [] = false
contains-lit l (x ∷ xs) with lit-eq l x
... | true  = true
... | false = contains-lit l xs

-- removes a literal

remove-lit : Literal → Clause → Clause
remove-lit l [] = []
remove-lit l (x ∷ xs) with lit-eq l x
... | true  = remove-lit l xs
... | false = x ∷ remove-lit l xs

--   l = true:
--   remove satisfied clauses
--   remove ¬l from remaining clauses

simplify : Literal → FormulaS → FormulaS
simplify l [] = []

simplify l (c ∷ cs) with contains-lit l c
... | true = simplify l cs
... | false = remove-lit (negate-lit l) c ∷ simplify l cs

-- looks for empty clause

has-empty-clause : FormulaS → Bool
has-empty-clause [] = false
has-empty-clause ([] ∷ _) = true
has-empty-clause (_ ∷ fs) = has-empty-clause fs

-- looks for unit clause

find-unit-clause : FormulaS → Maybe Literal
find-unit-clause [] = nothing
find-unit-clause ((l ∷ []) ∷ fs) = just l
find-unit-clause (_ ∷ fs) = find-unit-clause fs

-- look for pure literals

clause-lits : Clause → List Literal
clause-lits c = c

formula-lits : FormulaS → List Literal
formula-lits [] = []
formula-lits (c ∷ fs) = clause-lits c ++ formula-lits fs

occurs : Literal → FormulaS → Bool
occurs l [] = false
occurs l (c ∷ fs) with contains-lit l c
... | true  = true
... | false = occurs l fs

find-pure-from : List Literal → FormulaS → Maybe Literal
find-pure-from [] f = nothing

find-pure-from (l ∷ ls) f with occurs (negate-lit l) f
... | true  = find-pure-from ls f
... | false = just l

find-pure : FormulaS → Maybe Literal
find-pure f = find-pure-from (formula-lits f) f


first-literal-clause : Clause → Maybe Literal
first-literal-clause [] = nothing
first-literal-clause (l ∷ _) = just l

choose-literal : FormulaS → Maybe Literal
choose-literal [] = nothing

choose-literal (c ∷ fs) with first-literal-clause c
... | just l  = just l
... | nothing = choose-literal fs

-- count literals so we show that algorithm stops

count-lits : FormulaS → ℕ
count-lits [] = zero
count-lits (c ∷ fs) = length c + count-lits fs

-- actual dpll

dpll-iter : ℕ → FormulaS → Assignment → Maybe Assignment
dpll-iter zero f a = nothing

-- success = no clauses left
dpll-iter (suc n) [] a = just a

-- failure = contains empty clause
dpll-iter (suc n) f a with has-empty-clause f
... | true = nothing
... | false with find-unit-clause f

-- unit propagation
... | just l = dpll-iter n (simplify l f) (a [ lit-var l ]≔ lit-sign l)
... | nothing with find-pure f

-- pure literal elimination
... | just l = dpll-iter n (simplify l f) (a [ lit-var l ]≔ lit-sign l)
... | nothing with choose-literal f
... | nothing = just a

-- branching
... | just l with dpll-iter n (simplify l f) (a [ lit-var l ]≔ lit-sign l)
... | just sol = just sol
... | nothing = dpll-iter n (simplify (negate-lit l) f) (a [ lit-var (negate-lit l) ]≔ lit-sign (negate-lit l))



-- solver for cnf

solve-cnf : CNF → Maybe Assignment
solve-cnf f = dpll-iter (count-lits (cnf→formula f)) (cnf→formula f) empty

-- couple tests, can use ctrl c+n with solve-cnf test

test1 : CNF
test1 = Lit (Var 0) ∧ Disj (Lit (¬ 0))

test2 : CNF
test2 = (Var 0 ∨ Lit (Var 1)) ∧ Disj (Lit (Var 2))

test3 : CNF
test3 = (Var 0 ∨ Lit (Var 1)) ∧ (((¬ 0) ∨ Lit (Var 2)) ∧ Disj (Lit (¬ 2)))


-- 11. (Tseytin) -- 

--- Flip a literal's polarity. Needed to build Tseytin clauses. ---
neg-lit : Literal → Literal
neg-lit (Var n) = ¬ n
neg-lit (¬ n) = Var n

--- Append two CNFs, with Empty as identity. Needed to merge clause sets from recursive calls. --- 
_cnf-∧_ : CNF → CNF → CNF
Empty   cnf-∧ c  =  c
c       cnf-∧ Empty  =  c
Disj d  cnf-∧ c  =  d ∧ c
(d ∧ c₁) cnf-∧ c₂  =  d ∧ (c₁ cnf-∧ c₂)

--- Find the highest variable index in the formula so fresh variables can start above it. ---
--- Used ⊔ which is the maximum operator for natural numbers ---
max-var-nnf : NNF → ℕ
max-var-nnf (Lit (Var n)) = n
max-var-nnf (Lit (¬ n))   = n
max-var-nnf (A ∧ B)       = max-var-nnf A ⊔ max-var-nnf B
max-var-nnf (A ∨ B)       = max-var-nnf A ⊔ max-var-nnf B


tseytin-step : NNF → ℕ → (CNF × Literal × ℕ)
tseytin-step (Lit l) n = (Empty , l , n)
tseytin-step (A ∨ B) n  = 
  let (cA , repA , n1) = tseytin-step A n
      (cB , repB , n2) = tseytin-step B n1
      p = Var n2
      np = neg-lit p
      c1 = np ∨ (repA ∨ Lit repB) 
      c2 = p ∨ Lit (neg-lit repA)
      c3 = p  ∨ Lit (neg-lit repB)
      newClauses = c1 ∧ (c2 ∧ Disj c3)
  in ((cA cnf-∧ (cB cnf-∧ newClauses)) , p , suc n2)
tseytin-step (A ∧ B) n =
  let (cA , repA , n1) = tseytin-step A n
      (cB , repB , n2) = tseytin-step B n1
      p                = Var n2
      np               = neg-lit p
      c1               = np ∨ Lit repA
      c2               = np ∨ Lit repB                        
      c3               = p  ∨ (neg-lit repA ∨ Lit (neg-lit repB))
      newClauses       = c1 ∧ (c2 ∧ Disj c3)
  in ((cA cnf-∧ (cB cnf-∧ newClauses)) , p , suc n2)


to-cnf : NNF → CNF
to-cnf f =
  let start          = suc (max-var-nnf f)
      (clauses , rep , _) = tseytin-step f start
  in  clauses cnf-∧ Disj (Lit rep)
 
--- Tests for Tseyting ---
-- Literal: no fresh vars introduced, just wraps in Disj
_ : to-cnf (Lit (Var 0)) ≡ Disj (Lit (Var 0))
_ = refl

-- Conjunction: p2 ↔ (p0 ∧ p1), fresh var is 2
_ : to-cnf (Lit (Var 0) ∧ Lit (Var 1))
    ≡ ((¬ 2) ∨ Lit (Var 0)) ∧ (((¬ 2) ∨ Lit (Var 1)) ∧ ((Var 2 ∨ ((¬ 0) ∨ Lit (¬ 1))) ∧ Disj (Lit (Var 2))))
_ = refl

-- Disjunction: p2 ↔ (p0 ∨ p1), fresh var is 2
_ : to-cnf (Lit (Var 0) ∨ Lit (Var 1))
    ≡ ((¬ 2) ∨ (Var 0 ∨ Lit (Var 1))) ∧ ((Var 2 ∨ Lit (¬ 0)) ∧ ((Var 2 ∨ Lit (¬ 1)) ∧ Disj (Lit (Var 2))))
_ = refl

-- Semantic tests: eval-cnf on Tseytin output agrees with eval-nnf on original
-- (requires a consistent assignment where fresh vars match their subformula values)

-- {0→true, 1→true, 2→true}: consistent for ∧ since true∧true=true
aConj-sat : Assignment
aConj-sat = ((empty [ 0 ]≔ true) [ 1 ]≔ true) [ 2 ]≔ true

-- {0→true, 1→false, 2→false}: consistent for ∧ since true∧false=false
aConj-unsat : Assignment
aConj-unsat = ((empty [ 0 ]≔ true) [ 1 ]≔ false) [ 2 ]≔ false

-- conjunction: satisfiable case
_ : eval-cnf aConj-sat (to-cnf (Lit (Var 0) ∧ Lit (Var 1))) ≡ eval-nnf aConj-sat (Lit (Var 0) ∧ Lit (Var 1))
_ = refl

-- conjunction: unsatisfied case
_ : eval-cnf aConj-unsat (to-cnf (Lit (Var 0) ∧ Lit (Var 1))) ≡ eval-nnf aConj-unsat (Lit (Var 0) ∧ Lit (Var 1))
_ = refl

-- disjunction: myMap = {0→true, 1→false, 2→true}, consistent since true∨false=true
_ : eval-cnf myMap (to-cnf (Lit (Var 0) ∨ Lit (Var 1))) ≡ eval-nnf myMap (Lit (Var 0) ∨ Lit (Var 1))
_ = refl


-- 12. --

data Input : Set where
  formula : Formula → Input
  nnf     : NNF → Input
  cnf     : CNF → Input

solve : Input → Maybe Assignment
solve (formula f) = solve-cnf (to-cnf (to-nnf f))
solve (nnf f) = solve-cnf (to-cnf f)
solve (cnf f) = solve-cnf f


-- solve (formula (f))
-- solve (nnf (n))
-- solve (cnf (c))
