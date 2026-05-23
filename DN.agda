module DN where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
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


-- test
_ : eval myMap (Var 0 ∧ Var 1) ≡ just false
_ = refl

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


-- test

_ : eval-nnf myMap ((Lit (Var 0) ∧ Lit (¬ 1)) ∧ Lit (Var 0)) ≡ just true
_ = refl

_ : eval-nnf myMap (Lit (Var 0) ∧ Lit (Var 99)) ≡ nothing
_ = refl



-- 7. --
-- Literal already defined

data Disjunct : Set where
  Lit : Literal → Disjunct
  _∨_ : Literal → Disjunct → Disjunct

data CNF : Set where
  Disj : Disjunct → CNF
  _∧_ : Disjunct → CNF → CNF


-- 8. --

-- Disjunction helper

eval-disj : Assignment → Disjunct → Maybe Bool
eval-disj a (Lit l)  = eval-lit a l

eval-disj a (f ∨ g) with eval-lit a f | eval-disj a g
... | just b₁ | just b₂ = just (b₁ || b₂)
... | _       | _       = nothing


-- Evaluate CNF formula

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf a (Disj f) = eval-disj a f

eval-cnf a (f ∧ g) with eval-disj a f | eval-cnf a g
... | just b₁ | just b₂ = just (b₁ && b₂)
... | _       | _       = nothing


-- test

_ : eval-cnf myMap (((¬ 0) ∨ Lit (Var 1)) ∧ Disj (Lit (Var 2))) ≡ just false
_ = refl

_ : eval-cnf myMap (Disj (Var 99 ∨ Lit (Var 0))) ≡ nothing
_ = refl
