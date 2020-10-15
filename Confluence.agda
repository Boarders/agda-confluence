module Confluence where

open import Data.List
  using (List; []; _∷_)
open import Relation.Nullary
   using (¬_)
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Product
  using (Σ-syntax; _×_) renaming (_,_ to Pr)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one : ℕ
one = succ zero


data _* {a} (↦ : a → a → Set) : (a → a → Set) where

  _∎ : ∀ (M : a)
    → (↦ *) M M

  _↦⟨_⟩_ : (L : a) {M N : a}
    → ↦ L M
    → (↦ *) M N
    → (↦ *) L N

num-steps : ∀ {a} {↦ : a → a → Set} {l1 l2 : a} → (↦ *) l1 l2 → ℕ
num-steps (_ ∎) = zero
num-steps (_ ↦⟨ st ⟩ steps) = succ (num-steps steps)

lift :  ∀ {a} {↦ : a → a → Set} {l1 l2 : a} → ↦ l1 l2 → (↦ *) l1 l2
lift {_} {_} {l1} {l2} st = l1 ↦⟨ st ⟩ (l2 ∎)

diamond : ∀ {a : Set} → (↦ : a → a → Set) → {l1 l2 l3 : a} → Set
diamond {a} ↦ {l} {l1} {l2} =  ↦ l l1 → ↦ l l2 → Σ[ l3 ∈ a ] (↦ l1 l3 × ↦ l2 l3)

confluence : ∀ {a : Set} → (↦ : a → a → Set) → {l1 l2 l3 : a} → Set
confluence {a} ↦ {l} {l1} {l2} =  diamond (↦ *) {l} {l1} {l2}

right-confluence : ∀ {a : Set} → (↦ : a → a → Set) → {l1 l2 l3 : a} → Set
right-confluence {a} ↦ {l1} {l2} {l3} =  
  ↦ l1 l2 → (l1↦*l3 : (↦ *) l1 l3)
  → Σ[ l4 ∈ a ] (↦ l3 l4 × (Σ[ l2↦*l4 ∈ (↦ *) l2 l4 ] (num-steps l2↦*l4 ≡ num-steps l1↦*l3)))



diamond⇒right-confluence : 
   ∀ {a : Set} (l l1 l2 : a) → (↦ : a → a → Set)
   → (∀ {l1 l2 l3} → diamond ↦ {l1} {l2} {l3}) → right-confluence ↦ {l} {l1} {l2}
diamond⇒right-confluence {a} l l1 l2 ↦ diamP l↦*l1 l↦*l2 = {!!}
  where
  go 
    : ∀  {l1 l2 l3 : a} 
    → (st1 : ↦ l1 l2) → (l1↦*l3 : (↦ *) l1 l3) 
    → Σ[ l4 ∈ a ] (↦ l3 l4 × (Σ[ l2↦*l4 ∈ (↦ *) l2 l4 ] (num-steps l2↦*l4 ≡ num-steps l1↦*l3)))
  go {l1} {l2} st1 (_ ∎) = Pr l2 (Pr st1 (Pr (l2 ∎) refl))
  go {l1} {l2} l1↦l2 (_↦⟨_⟩_ _ {m1} l1↦m1 m1↦*l3) with diamP {l1} {l2} {m1} l1↦l2 l1↦m1
  ... | Pr m2 (Pr l2↦m2 m1↦m2) with go m1↦m2 m1↦*l3 
  ... | Pr l4 (Pr l3↦l4 (Pr m2↦*m4 eq)) 
    = Pr l4 (Pr l3↦l4 (Pr (l2 ↦⟨ l2↦m2 ⟩ m2↦*m4) (cong succ eq)))


diamond⇒confluence : 
   ∀ {a : Set} (l l1 l2 : a) → (↦ : a → a → Set)
   → (∀ {l1 l2 l3} → diamond ↦ {l1} {l2} {l3}) → confluence ↦ {l} {l1} {l2}
diamond⇒confluence {a} l l1 l2 ↦ diamP l↦*l1 l↦*l2 = 
    go (num-steps l↦*l1) (num-steps l↦*l2) l↦*l1 l↦*l2 refl refl
  where
  go
    : ∀  {l1 l2 l3 : a} 
    → (n1 : ℕ) → (n2 : ℕ) → (st1 : (↦ *) l1 l2) → (st2 : (↦ *) l1 l3) 
    → num-steps st1 ≡ n1
    → num-steps st2 ≡ n2
    →  Σ[ l4 ∈ a ] ((↦ *) l2 l4 × (↦ *) l3 l4)
  go {l1} zero zero (_ ∎) (_ ∎) pf1 pf2 = Pr l1 (Pr (l1 ∎) (l1 ∎))
  go {l1} {_} {l3} zero (succ n2) (.l1 ∎) st2 pf1 pf2 = Pr l3 (Pr st2 (l3 ∎))
  go {l1} {l2} (succ n1) zero st1 (_ ∎) pf1 pf2 = Pr l2 (Pr (l2 ∎) st1)
  go {l1} {l2} {l3} (succ n2@.(num-steps m2↦*l2)) (succ n3@.(num-steps m3↦*l3)) (_↦⟨_⟩_ .l1 {m2} l1↦m2 m2↦*l2) (_↦⟨_⟩_ .l1 {m3} l1↦m3 m3↦*l3) refl refl 
    with (λ a1 a2 a3 n st1 st2 pf1 pf2 → go {a1} {a2} {a3} (succ n2) n3 st1 st2)
  ... | rec  = {!!}
--    with diamP l1↦m2 l1↦m3
--  ... | Pr m4 (Pr m2↦m4 m3↦m4) 
--          with 
--            go {m3} {m4} {l3} one n3 (lift m3↦m4) m3↦*l3 refl refl
--  ... | Pr l4 (Pr m4↦*l4 l3↦*l4) 
--          with 
--            go {m2} {l2} {l4} n2 (succ (num-steps m4↦*l4)) 
--               m2↦*l2 (m2 ↦⟨ m2↦m4 ⟩ m4↦*l4) refl refl 
--  ... | sg =  {!!}

