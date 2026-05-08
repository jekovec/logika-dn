module DN where

open import Data.Nat using (ℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)



-- 1. --
data Formula : Set where
  Var : ℕ → Formula
  ¬_  : Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula

-- 2. -- 
data Literal : Set where
  Var : ℕ → Literal
  ¬_  : ℕ → Literal

data NNF : Set where
  Lit : Literal → NNF
  _∧_ : NNF → NNF → NNF
  _∨_ : NNF → NNF → NNF


-- 3. -- 
mutual
    to-nnf : Formula → NNF
    to-nnf (Var f) = Lit (Var f)
    to-nnf (f ∧ g) = to-nnf f ∧ to-nnf g
    to-nnf (f ∨ g) = to-nnf f ∨ to-nnf g
    to-nnf (¬ f) = to-nnf-neg f 

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
