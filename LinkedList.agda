open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality
-- Why on earch isn't ≡ in the prelude?
open import Data.Maybe
open import RGref

module LinkedList where
-- Prepend-only Linked list
   {- Unlike the Coq implementation, defining the prepend-only linked list is
      totally straightforward, no wonky encoding and extra impredicativity required -}
  mutual
    data LList : Set where
       LNil : LList
       LCons : (n : ℕ) -> (tl : Ref LList any limm limm) -> LList
    data limm  (l1 : LList) (l2 : LList) : heap -> heap -> Set where
       limm_nil : ∀ h h' -> l1 ≡ LNil -> l2 ≡ LNil -> limm l1 l2 h h'
       limm_cons : forall (n : ℕ) (tl : Ref LList any limm limm) h h' ->
                   limm (_[_] h tl) (_[_] h' tl) h h' ->
                   l1 ≡ (LCons n tl) ->
                   l2 ≡ (LCons n tl) ->
                   limm l1 l2 h h'
  listref = Ref LList any limm limm

  mkNil : (u : Unit) -> ● (Ref LList (\l h → l ≡ LNil) limm limm)
  mkNil = \u → alloc (\l h → l ≡ LNil) limm limm LNil (λ e → refl)

  mkCons : (n : ℕ) -> (tl : Ref LList any limm limm) -> ● (Ref LList (\l h → l ≡ LCons n tl) limm limm)
  mkCons n tl = alloc (\l h → l ≡ LCons n tl) limm limm (LCons n tl) (\_ → refl)

  data r-prepend : hrel listref where
    r-prepend-nop : ∀ l h → r-prepend l l h h
    r-prepend-op : ∀ h h' i l (l' : Ref LList (\n h → n ≡ LCons i l) limm limm) →
                     r-prepend l (convert-P l' any (imply-any (λ z _ → z ≡ LCons i l))) h h'
  
  list-container = Ref listref any r-prepend r-prepend

  prefix : list-container -> ℕ -> ● Unit
  prefix cont n =
    (mkCons n (! cont)) >>=
    (\ x ->
         [ cont ]:=< convert-P x any (imply-any (λ z _ → z ≡ LCons n (! cont))) >
                (λ h → r-prepend-op h (h [ cont ↦ convert-P x (λ _ _ → ⊤) (imply-any (λ z _ → z ≡ LCons n (! cont))) ])
                                    n (! cont) x))

