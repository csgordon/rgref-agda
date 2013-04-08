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

module RGref where
  data heap : Set where

  -- NOTE: For types, never use T, always use t or τ or something else; the capital T looks too much like top (⊤) in my terminal
  
  -- Heap predicates and relations
  hpred : Set -> Set1
  hpred τ = τ -> heap -> Set
  hrel : Set -> Set1
  hrel τ = τ -> τ -> heap -> heap -> Set

  -- Stable predicates
  stable : {τ : Set} -> (P : hpred τ) -> (R : hrel τ) -> Set
  stable P R = ∀ a b h1 h2 -> P a h1 -> R a b h1 h2 -> P b h2

  -- Handy reusable predicates and relations, and nice properties thereof
  any : {τ : Set} -> hpred τ
  any = \a h → ⊤

  any-stable : ∀ τ (R : hrel τ) -> stable any R
  any-stable τ R = \ a b h1 h2 pf1 pfR → tt

  havoc : {τ : Set} -> hrel τ
  havoc = \a a' h h' → ⊤

  locally-const : {τ : Set} -> hrel τ
  locally-const = \a a' h h' → a ≡ a'

  -- Implications, intersections among predicates and relations
  _⊆_ : {τ : Set} -> hpred τ -> hpred τ -> Set
  P ⊆ Q = ∀ a h -> P a h -> Q a h
  _⊑_ : {τ : Set} -> hrel τ -> hrel τ -> Set
  R ⊑ S = ∀ a a' h h' -> R a a' h h' -> S a a' h h'

  _∩_ : {τ : Set} -> hpred τ -> hpred τ -> hpred τ
  P ∩ Q = \a h → P a h × Q a h
  _⋂_ : {τ : Set} -> hrel τ -> hrel τ -> hrel τ
  R ⋂ S = λ a b h i → R a b h i × S a b h i

  -- Handy common implications
  imply-any : ∀ {τ} -> (P : hpred τ) -> P ⊆ any
  imply-any P a h pf = tt

  -- Main reference type
  data Ref (T : Set) (P : hpred T) (R : hrel T) (G : hrel T) : Set where

  -- Heap Axioms
  postulate
    -- Heap select
    _[_] : heap -> {T : Set} {P : T -> heap -> Set} {R : T -> T -> heap -> heap -> Set} {G : T -> T -> heap -> heap -> Set} -> Ref T P R G -> T
    -- Heap update
    _[_↦_] : heap -> {T : Set} {P : T -> heap -> Set} {R : T -> T -> heap -> heap -> Set} {G : T -> T -> heap -> heap -> Set} -> Ref T P R G -> T -> heap
    -- A deref primitive, TODO: IGNORING FOLDING FOR NOW
    !_ : {T : Set} {P : T -> heap -> Set} {R : T -> T -> heap -> heap -> Set} {G : T -> T -> heap -> heap -> Set} -> Ref T P R G -> T
    convert-P : {T : Set} {P : hpred T} {R : hrel T} {G : hrel T} (r : Ref T P R G) (P' : hpred T) (pf : P ⊆ P') -> Ref T P' R G

  -- Proof Axioms
  postulate
    -- conversion doesn't affect what properties are true of a heap select
    conversion-eq : {T : Set} {P : hpred T} {P' : hpred T} {R : hrel T} {G : hrel T}
                    (r : Ref T P R G) (pf : P ⊆ P') (h : heap) -> (_[_] h r) ≡ (_[_] h (convert-P r P' pf))
    conversion-eq' : {T : Set} {P : hpred T} {P' : hpred T} {R : hrel T} {G : hrel T}
                    (r : Ref T P R G) (pf : P ⊆ P') (h : heap) (I : T -> Set) -> I (_[_] h r) -> I (_[_] h (convert-P r P' pf))

  -- Monadic Axioms
  postulate
    -- RGref monad, TODO: IMPLEMENT SUBSTRUCTURAL SUPPORT
    {- Implementing substructural support for the ● monad will be painful.  Agda doesn't seem to have any obvious equivalent of Coq's Program extension,
       and web searches for "agda anonymous holes" and the like yield nothing useful, so for the moment I don't know how to guide the instantiation
       of proof terms that should be implicit in the syntax. -}
    ● : Set -> Set
    -- monadic bind
    _>>=_ : ∀ {T T'} -> ● T -> (T -> ● T') -> ● T'
    -- monadic return
    return : ∀ {T} -> T -> ● T
    -- monadic write operation
    {- TODO: make Gpf implicit!  Right now it's explicit b/c when I make it implicit, Agda identifies an unsolved meta-variable for the proof term,
       but I can't figure out how to instantiate it without making the proof term itself explicit. -}
    [_]:=<_> : ∀ {T P R G} -> (r : Ref T P R G) -> (e : T) -> (Gpf : ∀ (h : heap) -> G (! r) e h (h [ r ↦ e ])) -> ● Unit
    -- monadic alloc
    {- TODO: stability checks, precision, self-splitting, etc. -}
    alloc : ∀ {τ} P R G -> (e : τ) -> (∀ h → P e h) -> ● (Ref τ P R G)

  infixl 50 _>>=_



