module WT where
-- Well typed terms, conversion, and proof of soundness/completeness of decision procedure.

open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Bool hiding  (_≟_)  -- true/false,  T predicate
open import Data.Nat hiding (_≥_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality 
import Level as Lvl

open import Closures
open import NatProperties
open import PT
open import Kripke
open import SN


infix 12  _⟪_⟫
infix 11  _★_ 
infix 10 ∶∶λ_⇨_  

mutual 
  data Tm : Set where
    ⌜_⌝ : (x : Name) → Tm
    ∶∶λ_⇨_ : Name → Tm → Tm
    _★_ : Tm → Tm → Tm
    _⟪_⟫ : Tm → S → Tm

  data S : Set where
    idˢ : S
    _[_↠_] : S → Name → Tm → S     -- no constraint about whether x occurs in s. 
    _⊛_ : S → S → S      -- composes backward like function composition.



infix 10 _⊢_∶_  _⊢ˢ_∶_

-- Typing rules   ʷ means well-typed-terms.   above, e.g. <ʷ it means 'worlds'.
mutual 
  data _⊢_∶_  : (Γ : Context) (t : Tm) (A : Type) → Set where
    ↑ʷ[_]⟨_⟩ : ∀ {Γ Δ A t} (c : Γ ≥ Δ) (tt : Δ ⊢ t ∶ A) → Γ ⊢ t ∶ A
    _↳ʷ_ : ∀ {Γ A} x (occ : [ x ∶ A ]∈ Γ) → Γ ⊢ ⌜ x ⌝ ∶ A
    ∶∶λʷ : ∀ {Γ x A B f t} (tb : (Γ ∙[ x ∶ A ]⊣ f)  ⊢  t  ∶  B) → Γ ⊢ ∶∶λ x ⇨ t ∶ A ⇒ B
    _★ʷ_ : ∀ {Γ A B} {t t' : Tm} (tt : Γ ⊢  t  ∶  A ⇒ B) (tt : Γ ⊢  t' ∶  A) → Γ  ⊢ (t ★ t') ∶ B
    _⟪_⟫ʷ : ∀ {Γ A Δ s t} (tt : Δ ⊢ t ∶ A) (ts : Γ ⊢ˢ s ∶ Δ)  → Γ  ⊢ (t ⟪ s ⟫) ∶ A
  
  data _⊢ˢ_∶_ : (Γ : Context) (s : S) (Δ : Context) → Set where
    ↑ʷˢ_∙_ : ∀ {Θ Γ Δ s} (c : Θ ≥ Γ) (ts : Γ ⊢ˢ s ∶ Δ) → Θ ⊢ˢ s ∶ Δ
    πʷˢ_∙_ : ∀ {Δ Θ Γ s} (c : Δ ≥ Θ) (ts : Γ ⊢ˢ s ∶ Δ) → Γ ⊢ˢ s ∶ Θ
    idʷˢ : ∀ {Γ} → Γ ⊢ˢ idˢ ∶ Γ
    _[_↠ʷˢ_] : ∀ {Γ Δ} {s : S} (ts : Γ ⊢ˢ s ∶ Δ) x {A} {f : T(x # Δ)} {s t} (tt : Γ ⊢ t ∶ A) → Γ ⊢ˢ (s [ x ↠ t ]) ∶ (Δ ∙[ x ∶ A ]⊣ f)
    _⊛ʷˢ_ : ∀ {Γ Δ Θ s₁ s₂} (ts₂ : Δ ⊢ˢ s₂ ∶ Θ) (ts₁ : Γ ⊢ˢ s₁ ∶ Δ)  → Γ ⊢ˢ (s₂ ⊛ s₁) ∶ Θ



infix 10 _⊢_≅_∶_  _⊢ˢ_≅_∶_
-- Convertibility of well-typed terms.  These are partial equivalence relations (symmetric / transitive)
mutual
  data _⊢_≅_∶_ : ∀ (Γ : Context)(t₁ t₂ : Tm)(A : Type) → Set where
    
    ∶cλ : ∀ {Γ A B t t' x f} (eq : (Γ ∙[ x ∶ A ]⊣ f) ⊢ t ≅ t' ∶ B) → Γ ⊢ ∶∶λ x ⇨ t ≅ ∶∶λ x ⇨ t' ∶ A ⇒ B
    ∶c★₁ : ∀ {Γ A B t t' t''} (eq : Γ ⊢ t ≅ t' ∶ A ⇒ B) (tt'' : Γ ⊢ t'' ∶ A)  →  Γ ⊢ t ★ t'' ≅ t' ★ t'' ∶ B
    ∶c★₂ : ∀ {Γ A B t t' t''} (tt : Γ ⊢ t ∶ A ⇒ B) (eq : Γ ⊢ t' ≅ t'' ∶ A)  →  Γ ⊢ t ★ t'' ≅ t' ★ t'' ∶ B
    ∶c⟪⟫₁ : ∀ {Γ Δ A t t' s }  (eqt : Γ ⊢ t ≅ t' ∶ A)  (ts : Δ ⊢ˢ s ∶ Γ)  →  Δ ⊢ t ⟪ s ⟫ ≅ t' ⟪ s ⟫ ∶ A
    ∶c⟪⟫₂ : ∀ {Γ Δ A t s s' } (tt : Γ ⊢ t ∶ A)  (eqs : Δ ⊢ˢ s ≅ s' ∶ Γ)  →  Δ ⊢ t ⟪ s ⟫ ≅ t ⟪ s' ⟫ ∶ A
    refl-wt : ∀ {Γ t A} (tt : Γ ⊢ t ∶ A) → Γ ⊢ t ≅ t ∶ A
    ∶∶β : ∀ {Γ Δ s x A B f t₁ t₂} (ts : Γ ⊢ˢ s ∶ Δ) (tt₁ : (Δ ∙[ x ∶ A ]⊣ f) ⊢ t₁ ∶ B) (tt₂ : Γ ⊢ t₂ ∶ A) 
                         → Γ ⊢ ((∶∶λ x ⇨ t₁) ⟪ s ⟫) ★ t₂ ≅ t₁ ⟪ s [ x ↠ t₂ ] ⟫ ∶ B
    ∶∶η  :  ∀ {Γ A B t x} (f : T(x # Γ)) (tt : Γ ⊢ t ∶ A ⇒ B) → Γ ⊢ t ≅ ∶∶λ x ⇨ t ★ ⌜ x ⌝ ∶ A ⇒ B
    ∶∶wk  :  ∀ {Γ Δ A t₁ t₂} (c : Γ ≥ Δ) (eq  : Δ ⊢ t₁ ≅ t₂ ∶ A) → Γ ⊢ t₁ ≅ t₂ ∶ A
    ∶∶v₁  : ∀{Γ Δ A x s t} (f : T(x # Δ)) (ts : Γ ⊢ˢ s ∶ Δ) (tt : Γ ⊢ t ∶ A) → Γ ⊢ ⌜ x ⌝ ⟪ s [ x ↠ t ] ⟫ ≅ t ∶ A
    ∶idsub : ∀{Γ t A } (tt : Γ ⊢ t ∶ A) → Γ ⊢ t ⟪ idˢ ⟫ ≅ t ∶ A
    ∶∶sapp : ∀ {Γ Δ A B t₁ t₂ s} (tt₁ :  Δ ⊢ t₁ ∶ A ⇒ B) (tt₂ : Δ ⊢ t₂ ∶ A) (ts : Γ ⊢ˢ s ∶ Δ) → Γ ⊢ (t₁ ★ t₂) ⟪ s ⟫ ≅ t₁ ⟪ s ⟫ ★ t₂ ⟪ s ⟫ ∶ B
    ∶∶s⊙  : ∀ {Γ₁ Γ₂ Γ₃ A s₁ s₂ t} (ts₁ : Γ₂ ⊢ˢ s₁ ∶ Γ₃) (ts₂ : Γ₁ ⊢ˢ s₂ ∶ Γ₂) (tt : Γ₃ ⊢ t ∶ A) → Γ₁ ⊢ (t ⟪ s₁ ⟫) ⟪ s₂ ⟫ ≅ t ⟪ s₂ ⊛ s₁ ⟫ ∶ A
    -- TODO add sym-trans

    

  data _⊢ˢ_≅_∶_ : ∀ (Γ : Context) (s₁ s₂ : S) (Δ : Context) → Set where
    c⊛₁ : ∀ { Γ₁ Γ₂ Γ₃ s₁ s₂ s₃} (ts₃ : Γ₁ ⊢ˢ s₃ ∶ Γ₂)(eq₁₂ : Γ₂ ⊢ˢ s₁ ≅ s₂ ∶ Γ₃) → Γ₁ ⊢ˢ s₁ ⊛ s₃ ≅ s₂ ⊛ s₃ ∶ Γ₃
    c⊛₂ : ∀ { Γ₁ Γ₂ Γ₃ s₁ s₂ s₃} (eq₂₃ : Γ₁ ⊢ˢ s₂ ≅ s₃  ∶ Γ₂)(ts₁ : Γ₂ ⊢ˢ s₁ ≅ s₂ ∶ Γ₃) → Γ₁ ⊢ˢ s₁ ⊛ s₂ ≅ s₁ ⊛ s₃ ∶ Γ₃
    c↠₁ : ∀ {Δ Γ A s₁ s₂ t x f } (tt : Δ ⊢ t ∶ A) (eqs : Δ ⊢ˢ s₁ ≅ s₂ ∶ Γ)  →  Δ ⊢ˢ s₁ [ x ↠ t ] ≅ s₂ [ x ↠ t ] ∶ (Γ ∙[ x ∶ A ]⊣ f)
    c↠₂ : ∀ {Δ Γ A s t₁ t₂ x f } (eqt : Δ ⊢ t₁ ≅ t₂ ∶ A) (ts : Δ ⊢ˢ s ∶ Γ)  → Δ ⊢ˢ s [ x ↠ t₁ ] ≅ s [ x ↠ t₂ ] ∶ (Γ ∙[ x ∶ A ]⊣ f)
    ∶↑eqˢ : ∀ {Γ₁ Γ₂ Δ s₁ s₂} (c : Γ₁ ≥ Γ₂) (eq : Γ₂ ⊢ˢ s₁ ≅ s₂ ∶ Δ) → Γ₁ ⊢ˢ s₁ ≅ s₁ ∶ Δ
    ∶projeqˢ : ∀ {Δ₁ Δ₂ Γ s₁ s₂} (c : Δ₁ ≥ Δ₂) (eq : Γ ⊢ˢ s₁ ≅ s₂ ∶ Δ₁) → Γ ⊢ˢ s₁ ≅ s₂ ∶ Δ₂ 
    ∶idˢleft  : ∀ {Γ Δ s} (ts : Γ ⊢ˢ s ∶ Δ) → Γ ⊢ˢ idˢ ⊛ s ≅ s ∶ Δ
    ∶idˢright  : ∀ {Γ Δ s} (ts : Γ ⊢ˢ s ∶ Δ) → Γ ⊢ˢ s ⊛ idˢ ≅ s ∶ Δ
    ∶⊛-assoc : ∀ {Γ₁ Γ₂ Γ₃ Δ s₁ s₂ s₃} (ts₃ : Γ₁ ⊢ˢ s₃ ∶ Γ₂) (ts₂ : Γ₂ ⊢ˢ s₂ ∶ Γ₃) (ts₁ : Γ₃ ⊢ˢ s₁ ∶ Δ) → Γ₃  ⊢ˢ (s₁ ⊛ s₂) ⊛ s₃ ≅ s₁ ⊛ (s₂ ⊛ s₃) ∶ Δ
    ∶⊛-ext  : ∀ {Γ₁ Γ₂ Δ A x f s₁ s₂ t} (ts₂ : Γ₁ ⊢ˢ s₂ ∶ Γ₂) (ts₁ : Γ₂ ⊢ˢ s₁ ∶ Δ)  (tt : Γ₂ ⊢ t ∶ A)  
                         →  Γ₁ ⊢ˢ (s₁ [ x ↠ t ]) ⊛ s₂ ≅ (s₁ ⊛ s₂) [ x ↠ t ⟪ s₂ ⟫ ]  ∶  Δ ∙[ x ∶ A ]⊣ f
    ∶εeqid : ∀ {Γ s} (ts : Γ ⊢ˢ s ∶ ε) → Γ ⊢ˢ s ≅ idˢ ∶ ε 
    ∶∶ηε : ∀ {Γ Δ s x A f } (ts : Γ ⊢ˢ s ∶  Δ ∙[ x ∶ A ]⊣ f) 
                         → Γ ⊢ˢ s ≅ s [ x ↠ ⌜ x ⌝ ⟪ s ⟫ ] ∶  Δ ∙[ x ∶ A ]⊣ f    -- s WTyped at Δ and [Δ, x : A]  by implicit coercion ('π c' erased)
    ∶∶π∶ext : ∀ {Γ Δ A x s t} (f : T(x # Δ)) (ts : Γ ⊢ˢ s ∶ Δ) (tt : Δ ⊢ t ∶ A) →  Γ ⊢ˢ s [ x ↠ t ] ≅ s ∶ Δ
    -- TODO add sym-trans


-- could use SymTran closure. I'm not sure it's worth it. 
-- _⊢_≅_∶_  : ∀ (Γ : Context) (t t' : Tm) (A : Type) → Set
-- Γ ⊢ t ≅ t' ∶ A = t ≡[ (λ t₁ t₂ →  (_⊢_≐_∶_) Γ t₁ t₂ A)  ]* t'  
-- 
-- _⊢_≅ˢ_∶_  : ∀ (Γ : Context) (s t : S) (Δ : Context) → Set
-- Γ ⊢ s ≅ˢ s' ∶ Δ = s ≡[ ((λ s₁ s₂ → (_⊢_≐ˢ_∶_) Γ s₁ s₂ Δ))  ]* s'  
-- ask Randy.


conv⇒wtl : ∀ {Γ A t t'} (eqt : Γ ⊢ t ≅ t' ∶ A) →  Γ ⊢ t ∶ A 
conv⇒wtl eqt = {!!} 
conv⇒wtr : ∀ {Γ A t t'} (eqt : Γ ⊢ t ≅ t' ∶ A) →  Γ ⊢ t' ∶ A 
conv⇒wtr eqt = {!!}

conv⇒wtlˢ : ∀ {Δ Γ s s'} (eqs : Δ ⊢ˢ s ≅ s' ∶ Γ) →  Δ ⊢ˢ s ∶ Γ 
conv⇒wtlˢ eqs = {!!}
conv⇒wtrˢ : ∀ {Δ Γ s s'} (eqs : Δ ⊢ˢ s ≅ s' ∶ Γ) →  Δ ⊢ˢ s' ∶ Γ
conv⇒wtrˢ eqs = {!!}


-- proof tree erasure
mutual 
  _⁻ : ∀ {Γ A} (M : Γ ⊢ A) → Tm 
  _⁻ {Γ} [ .Γ ∋ x ↳ occ ] = ⌜ x ⌝
  (∶λ x # f ⇨ M) ⁻ = ∶∶λ x ⇨ (M ⁻)
  (M ⋆ N) ⁻ = (M ⁻) ★ (N ⁻)
  (M ⟨ γ ⟩) ⁻ = (M ⁻) ⟪ γ ⁻ˢ ⟫

  _⁻ˢ  : ∀ {Δ Γ} (γ : Δ ⇛ Γ) → S
  (π c) ⁻ˢ = idˢ
  (γ ⊙ δ) ⁻ˢ = (γ ⁻ˢ) ⊛ (δ ⁻ˢ)
  (γ [ x ↦ M ]) ⁻ˢ = (γ ⁻ˢ) [ x ↠ (M ⁻) ]


lemma₁₂ : ∀ {Γ A} (M : Γ ⊢ A) → Γ ⊢ (M ⁻) ∶ A
lemma₁₂ M = {!!}

-- note that we can have (M ⁻) ≡ (N ⁻) with M ≢ N. example just use different types.
-- t₁ = ∶λ x : A # f → ((Γ [ x : A ]⊣ f) ∋ x ↳ here!)     
-- t₂ = ∶λ x : B # f → ((Γ [ x : A ]⊣ f) ∋ x ↳ here!)  
-- both erase to ∶∶λ x . ⌜ x ⌝ 

infix 9 [_,_]_⟰ˢ_ [_,_]_⟰_ 
-- define relation between terms/substitutions and possible decorations
mutual 
  data [_,_]_⟰_ : ∀ Γ A (t : Tm) (M : Γ ⊢ A) → Set where
    c1 : ∀ {Γ : Context}{A : Type} (x : Name) (occ : [ x ∶ A ]∈ Γ)  →  [ Γ , A ]  (⌜ x ⌝) ⟰  [ Γ ∋ x ↳ occ ]
    c2 : ∀ {Γ A B t₁ t₂ M N } (d : [ Γ , A ⇒ B ] t₁ ⟰ M) (d : [ Γ , A ] t₂ ⟰ N) →  [ Γ , B ] (t₁ ★ t₂) ⟰ (M ⋆ N)
    c3 : ∀ {Γ Δ A t M }  (c : Δ ≥ Γ)  (d : [ Γ , A ] t ⟰ M) → [ Δ , A ] t ⟰ M ⟨ π c ⟩
    c4 : ∀ {Γ Δ A s γ t} {M : Γ ⊢ A} (d : [ Δ , Γ ] s ⟰ˢ γ)(d' : [ Γ , A ] t ⟰ M) → [ Δ , A ] t ⟪ s ⟫ ⟰ M ⟨ γ ⟩
    c5 : ∀ {Γ A B t x f M} (d : [ (Γ ∙[ x ∶ A ]⊣ f)  , B ] t ⟰ M) → [ Γ , A ⇒ B ] (∶∶λ x ⇨ t) ⟰ (∶λ x # f ⇨ M)
    
  data [_,_]_⟰ˢ_ : ∀ Δ Γ (s : S) (γ : Δ ⇛ Γ) → Set  where
    c1 : ∀ {Δ Γ } (c : Δ ≥ Γ) → [ Δ , Γ ] idˢ ⟰ˢ π c
    c2 : ∀ {Δ Γ A s γ t M x f} (d : [ Δ , Γ ] s ⟰ˢ γ) (d' : [ Δ , A ] t ⟰ M) → [ Δ , (Γ ∙[ x ∶ A ]⊣ f) ] (s [ x ↠ t ]) ⟰ˢ (γ [ x ↦ M ])
    c3 : ∀ {Θ Δ Γ s γ} (c : Δ ≥ Γ) (d : [ Θ , Δ ] s ⟰ˢ γ) → [ Θ , Γ ] s ⟰ˢ π c ⊙ γ
    c4 : ∀ {Θ Δ Γ s} {γ : Δ ⇛ Γ} (c : Θ ≥ Δ) (d : [ Δ , Γ ] s ⟰ˢ γ) → [ Θ , Γ ] s ⟰ˢ γ ⊙ π c
    c5 : ∀ {Θ Δ Γ s₁ s₂ γ₁ γ₂} (d₂ : [ Θ , Δ ] s₂ ⟰ˢ γ₂) (d₁ : [ Δ , Γ ] s₁ ⟰ˢ γ₁ ) → [ Θ , Γ ] s₁ ⊛ s₂ ⟰ˢ γ₁ ⊙ γ₂ 


mutual 
  lemma₁₃ : ∀ {Γ A } (M : Γ ⊢ A) → [ Γ , A ] (M ⁻) ⟰ M
  lemma₁₃ M = {!!} 

  lemsub₁₃ : ∀ {Δ Γ } (γ : Δ ⇛ Γ ) → [ Δ , Γ ] (γ ⁻ˢ) ⟰ˢ γ
  lemsub₁₃ γ = {!!} 


lemma₁₄ : ∀ {Γ A t} (tt : Γ ⊢ t ∶ A) → ∃ (λ (M : Γ ⊢ A) → (M ⁻) ≡ t)
lemma₁₄ wtt  = {!!} 

-- As a direct consequence of lemma₁₄ and lemma₁₃ we have 
lemma₁₅ : ∀ {Γ A t} (wtt : Γ ⊢ t ∶ A) → ∃ (λ (M : Γ ⊢ A) → [ Γ , A ] t ⟰ M)
lemma₁₅ wtt = {!!} 


-- As a consequence we can now define semantics of well-typed terms in a kripke model 
-- as the semantics of (the?) decorated term.  (better to say 'a'. no proof of uniqueness. )

-- recall that since many proof trees erase to curry-style typed terms we have no uniqueness.
-- however we can prove that if two proof trees of the same type (i.e. both Γ ⊢ A) are in η normal form 
-- and they are decorations of the same term, then the two proof terms are convertible. 
-- (Note that a term can have proof trees at multiple types, so this isn't the whole story)

mutual 
  lemma₁₆ : ∀ {Γ A t} (M N : Γ ⊢ A) (eM : enf M) (eN : enf N)(d₁ : [ Γ , A ] t ⟰ M)(d₂ : [ Γ , A ] t ⟰ N) → M ≡ N
  lemma₁₆ M N eM eN d₁ d₂ = {!!} 
 
  lanf₁ : ∀{Γ A B t} (M : Γ ⊢ A)(N : Γ ⊢ B) (aM : anf M) (aN : anf N) (d₁ : [ Γ , A ] t ⟰ M) (d₂ : [ Γ , B ] t ⟰ N) → A ≡ B 
  lanf₁ M N aM aN d₁ d₂ = {!!} 

  -- this appears to need heterogenous equality. ugh.
  lanf₂ : ∀{Γ A B t} (M : Γ ⊢ A)(N : Γ ⊢ B) (aM : anf M) (aN : anf N) (d₁ : [ Γ , A ] t ⟰ M) (d₂ : [ Γ , B ] t ⟰ N) →  H._≅_ M N 
  lanf₂ M N aM aN d₁ d₂ = {!!} 


--  proof : by lemma₁₆ and theorem₇ we get (nf N ≡ nf N)  and by theorem₅ we get Γ ⊢ A ∋ M ≅ N
corollary₂ : ∀ {Γ A} (M N : Γ ⊢ A) (eq : (nf M)⁻ ≡ (nf N)⁻) → Γ ⊢ A ∋ M ≅ N
corollary₂ M N eq = {!!}



--  Reduction.  What in the paper is called whnf is just β-normal form. (i.e. not eta long)
-- ∶∶λ x ⇨ t  is in β-nf if t ∈ β-nf 
-- t is in β-nf if t ∈ β-anf   
-- x is in β-anf
-- t₁ t₂ is in β-anf if t₁ ∈ β-anf and t₂ ∈ β-nf 
-- grammar =   t̂ ::= ∶∶λ x ⇨ t̂  | x t̂₁ ... t̂n

mutual 
  data βnf : ∀ (t : Tm) → Set where
    β-nf1 : ∀ (x : Name)(t : Tm)(pr : βnf t) → βnf (∶∶λ x ⇨ t)
    β-nf2 : ∀ (t : Tm)(pr : βanf t) → βnf t

  data βanf : ∀ (t : Tm) → Set where
    β-anf1 : ∀ (x : Name) → βanf ⌜ x ⌝
    β-anf2 : ∀ (t₁ t₂ : Tm)(pr₁ : βanf t₁)(pr₂ : βanf t₂) → βanf (t₁ ★ t₂)



infix 9 _⟶_  _⟶ˢ_ 
mutual 
  data _⟶_ : (t : Tm)(t' : Tm) → Set where
    c★₁⟶ :  ∀ {t t₁ t₂} (pr : t₁ ⟶ t₂) → t₁ ★ t ⟶ t₂ ★ t
    c⟪⟫₂⟶ : ∀ {s₁ s₂ x} (pr : s₁ ⟶ˢ s₂) → (⌜ x ⌝ ⟪ s₁ ⟫) ⟶ (⌜ x ⌝ ⟪ s₂ ⟫)
    β⟶ :  ∀ {t s t' x} → (∶∶λ x ⇨ t)⟪ s ⟫ ★ t' ⟶ t ⟪ s [ x ↠ t' ] ⟫ 
    v₁⟶ : ∀ {x s t} → ⌜ x ⌝ ⟪ s [ x ↠ t ] ⟫ ⟶ ⌜ x ⌝
    stepv⟶ :   ∀ { x y s t } (pr : T(not ⌊ x ≟ y ⌋)) →  ⌜ x ⌝ ⟪ s [ x ↠ t ] ⟫ ⟶  ⌜ x ⌝ ⟪ s ⟫
    idsub⟶ :  ∀ {x } → ⌜ x ⌝ ⟪ idˢ ⟫  ⟶  ⌜ x ⌝
    sapp⟶ :   ∀ {t₁ t₂ s} → (t₁ ★ t₂)⟪ s ⟫ ⟶ t₁ ⟪ s ⟫ ★ t₂ ⟪ s ⟫ 
    s⊛⟶ :   ∀ {t s₁ s₂ } → (t ⟪ s₁ ⟫) ⟪ s₂ ⟫ ⟶ t ⟪ s₁ ⊛ s₂ ⟫ 

  data  _⟶ˢ_ : (s : S)(s' : S) → Set where
    ∶⊛-assoc⟶ : ∀ {s₁ s₂ s₃} → (s₁ ⊛ s₂) ⊛ s₃ ⟶ˢ s₁ ⊛ (s₂ ⊛ s₃)
    ∶⊛-ext⟶ : ∀ {s₀ s₁ x t} → (s₀ [ x ↠ t ]) ⊛ s₁ ⟶ˢ (s₀ ⊛ s₁) [ x ↠ t ⟪ s₁ ⟫ ]
    idˢleft⟶ : ∀ {s} → idˢ ⊛ s ⟶ˢ s

_⟹_ : (t : Tm)(t' : Tm) → Set 
t ⟹ t' = t ▹[ _⟶_ ]* t'

infix 9 _⊢_↓_∶_  _⊢_↓η_∶_
mutual 
  data _⊢_↓_∶_  : (Γ : Context) (t : Tm) (t' : Tm) (A : Type) → Set where
    ♭↓ : ∀ {Γ t₀ t₁ t₂ } (p : t₀ ⟹ t₁) (q : Γ ⊢ t₁ ↓η t₂ ∶ ♭) → (Γ ⊢ t₀ ↓ t₂ ∶ ♭)
    fun↓ : ∀ {Γ A B t₁ t₂ } (p : (Γ ∙[ (fresh Γ) ∶ A ]⊣ (isfresh Γ)) ⊢ (t₁ ★ ⌜(fresh Γ)⌝) ↓ t₂ ∶ B) → (Γ ⊢ t₁ ↓ ∶∶λ (fresh Γ) ⇨ t₂ ∶ A ⇒ B)
 
  data _⊢_↓η_∶_  : (Γ : Context) (t : Tm) (t' : Tm) (A : Type) → Set where
    var↓ : ∀ {Γ A x } (occ : [ x ∶ A ]∈ Γ) → ( Γ ⊢ ⌜ x ⌝  ↓η  ⌜ x ⌝ ∶ A )
    ★↓ : ∀ {Γ A B t₁ t₁' t₂ t₂' } (p : Γ ⊢ t₁ ↓η t₁' ∶ A ⇒ B) (q : Γ ⊢ t₂ ↓ t₂' ∶ A) → ( Γ ⊢ t₁ ★ t₂ ↓η  t₁' ★ t₂' ∶ B )

_⊢_⇓_∶_ : (Γ : Context) (t : Tm) (t' : Tm) (A : Type) → Set 
Γ ⊢ t ⇓ t' ∶ A = Γ ⊢ t ⟪ idˢ ⟫ ↓ t' ∶ A


-- Want to prove M : Γ ⊢ A → Γ ⊢ (M)⁻ ⇓ (nf M)⁻ ∶ A
-- as is typical over red / eval relations for terms that compute must define logical relation.

-- Which kripke model??  In the initial/universal model
mutual  -- will inductive datatype work? 
  [_,_]_Ⓡ_ : ∀ Γ A (t : Tm) (v : Γ ⊩ A) → Set 
  [ Γ , ♭ ] t Ⓡ v = ∀ {Δ} (c : Δ ≥ Γ) (t' : Tm)(d : [ Δ  , ♭ ] t' ⟰ v c) → (Γ ⊢ t ↓ t' ∶ ♭) 
  [ Γ , A ⇒ B ] t Ⓡ v =  ∀ {Δ} (c : Δ ≥ Γ) (u : Δ ⊩ A) (t' : Tm) (wtt' : Δ ⊢ t' ∶ A) (p : [ Δ , A ] t' Ⓡ u) → ([ Δ , B ] (t ★ t') Ⓡ v c u)

  [_,_]_Ⓡˢ_ : ∀ Δ Γ (s : S) (ρ : Δ ⊩ᵉ Γ) → Set 
  [ Δ , ε ] s Ⓡˢ ρ = ⊤
  [ Δ , Γ ∙[ x ∶ A ]⊣ f ] s Ⓡˢ (ρ , v) =  ([ Δ , Γ ] s Ⓡˢ ρ) × ([ Δ  , A ] ⌜ x ⌝ ⟪ s ⟫ Ⓡ v)


-- lemmas 
lem17-1 : ∀ {Γ A} t₁ t₂ (v : Γ ⊩ A) (st : t₁ ⟶ t₂)(red : [ Γ , A ] t₂ Ⓡ v) → [ Γ , A ] t₁ Ⓡ v 
lem17-1 t₁ t₂ v st red = {!!} 

lem17-2 : ∀ {Δ Γ} s₁ s₂ (ρ : Δ ⊩ᵉ  Γ)(wts₁ :  Δ ⊢ˢ s₁ ∶ Γ)(st : s₁ ⟶ˢ s₂)(red : [ Δ , Γ ] s₂ Ⓡˢ ρ) → ([ Δ , Γ ] s₁ Ⓡˢ ρ)
lem17-2  s₁ s₂ ρ wts₁ st red  = {!!}

lem17-3 : ∀ {Δ Γ x A} s  (ρ : Δ ⊩ᵉ Γ)(occ : [ x ∶ A ]∈ Γ)(wts :  Δ ⊢ˢ s ∶ Γ) → [ Δ , A ] (⌜ x ⌝ ⟪ s ⟫) Ⓡ lookup Γ ρ occ 
lem17-3 s ρ occ wts = {!!} 

lem17-4 : ∀ {Δ Γ A} t (c : Δ ≥ Γ) (u : Γ ⊩ A) (red : [ Γ , A ] t Ⓡ u) → [ Δ , A ] t Ⓡ ↑[ c , A ]⟨ u ⟩ 
lem17-4 t c u red = {!!} 

lem17-5 : ∀ {Θ Δ Γ} s (c : Θ ≥ Δ) (wts : Δ ⊢ˢ s ∶ Γ) ( ρ : Δ ⊩ᵉ Γ)(red : [ Δ , Γ ] s Ⓡˢ ρ) → [ Θ , Γ ] s Ⓡˢ ↑ᵉ[ c , Γ ]⟨ ρ ⟩
lem17-5 s c wts ρ red = {!!} 

lem17-6 : ∀ {Γ Δ Θ} s (c : Γ ≥ Θ) (wts : Δ ⊢ˢ s ∶ Γ) (ρ : Δ ⊩ᵉ Γ)(red : [ Δ , Γ ] s Ⓡˢ ρ) → [ Δ , Θ ] s Ⓡˢ πᵉ c ρ
lem17-6 s c wts ρ red = {!!} 

-- surely we must need a freshness assumption here x # Γ ? wts doesn't tell us this.
lem17-7 : ∀ {Δ Γ A x} t s (wtt : Δ ⊢ t ∶ A)(wts : Δ ⊢ˢ s ∶ Γ)(ρ : Δ ⊩ᵉ Γ) (red :  [ Δ , Γ ] s Ⓡˢ ρ)(f : T(x # Γ )) → [ Δ , Γ ] (s [ x ↠ t ]) Ⓡˢ ρ
lem17-7 t s wtt wts ρ red = {!!} 

mutual 
   lem17-t :  ∀ {Δ Γ A } s t  (M : Γ ⊢ A) (ρ : Δ ⊩ᵉ Γ)(wts : Δ ⊢ˢ s ∶ Γ)(d : [ Γ , A ] t ⟰ M)(red : [ Δ , Γ ] s Ⓡˢ ρ) → [ Δ , A ] t ⟪ s ⟫ Ⓡ ⟦ M ⟧t ρ
   lem17-t M s t ρ wts d red = {!!}

   lem17-s :  ∀ {Γ Θ Δ} s₁ s₂  (γ : Γ ⇛ Θ)(ρ : Δ ⊩ᵉ Γ)(wts₂ : Δ ⊢ˢ s₂ ∶ Γ)(ds₁ : [ Γ , Θ ] s₁ ⟰ˢ γ)(rs₂ :  [ Δ , Γ ] s₂ Ⓡˢ ρ) → [ Δ , Θ ] s₂ ⊛ s₁ Ⓡˢ ⟦ γ ⟧s ρ 
   lem17-s  s₁ s₂  γ ρ wts₂ ds₁ rs₂ = {!!} 

-- finally 
mutual 
  -- intuitively that if  t Ⓡ u, u ∈ Γ ⊩ A, then Γ ⊢ t ↓ (reify u)⁻
  lemma₁₇ : ∀ {Γ A } t₀ t₁ (wtt₀ : Γ ⊢ t₀ ∶ A)(u : Γ ⊩ A)(rt₀  : [ Γ , A ] t₀ Ⓡ u) (dt₁ : [ Γ , A ] t₁ ⟰ (reify Γ A u)) → Γ ⊢ t₀ ↓ t₁ ∶ A
  lemma₁₇ t₀ t₁ wtt₀ u rt₀ dt₁ = {!!}

  lemma₁₇-val : ∀ {Γ A} t₀ (wtt₀ : Γ ⊢ t₀ ∶ A)(at₀ : βanf t₀)(f : Γ ⊢⇑ A) (h : ∀ {Δ} (c : Δ ≥ Γ) → (Δ ⊢ t₀ ↓η  (f c)⁻ ∶ A)) → [ Γ , A ] t₀ Ⓡ (val Γ A f)
  lemma₁₇-val t₀ wtt₀ at₀ f h = {!!} 

theorem₈ : ∀ {Γ A} t (M : Γ ⊢ A) (dt : [ Γ , A ] t ⟰ M) → Γ ⊢ t ⇓ (nf M)⁻ ∶ A
theorem₈ t M dt = {!!}

corollary₃ : ∀ {Γ A} t (M N : Γ ⊢ A)(dM : [ Γ , A ] t ⟰ M)(dN : [ Γ , A ] t ⟰ N) → (Γ ⊢ A ∋ M ≅ N)
corollary₃ t M N dM dN = {!!} 

-- Conversion soundness. 

-- proof by induction on the proof of t₀ ≅ t₁ (case refl we have t₀ , t₁ same, by corollary₃ get M ≅ N) 
theorem₉ : ∀ {Γ A} t₀ t₁ (M N : Γ ⊢ A)(dM : [ Γ , A ] t₀ ⟰ M)(dN : [ Γ , A ] t₁ ⟰ N)(teq : Γ ⊢ t₀ ≅ t₁ ∶ A) → Γ ⊢ A ∋ M ≅ N 
theorem₉ t₀ t₁ M N dM dN teq = {!!} 

-- completeness (proof by induction on M≅N)
theorem₁₀ : ∀ {Γ A } (M N : Γ ⊢ A)(eq : Γ ⊢ A ∋ M ≅ N) → Γ ⊢ (M)⁻ ≅ (N)⁻ ∶ A
theorem₁₀ M N eq = {!!} 

-- decision algorithm 
-- Theorem 11 : algorithm complete.
-- proof by lemma₁₄ and lemma₁₂ know ∃ proof trees M, N s.t. t₀ =M⁻, t₁=N⁻, by theorem₉ we get
-- that M ≅ N. choose (nf M)⁻ for t since, by lemma₈ Γ ⊢ M⁻ ⇓ (nf M)⁻ : A, Γ ⊢ N⁻ ⇓ (nf N)⁻ : A, 
-- and by theorem₆ we have (nf M) ≡ (nf N), hence (nf M)⁻ ≡ (nf N)⁻ 
theorem₁₁ : ∀ {Γ A} t₀ t₁ (teq : Γ ⊢ t₀ ≅ t₁ ∶ A) → ∃ (λ (t : Tm) → (Γ ⊢ t₀ ⇓ t ∶ A) × (Γ ⊢ t₁ ⇓ t ∶ A))
theorem₁₁ t₀ t₁ teq = {!!}

-- Theorem 12:  algorithm sound/correct
-- we have (nf M)⁻ ≡ (nf N)⁻ since by lemma₈ Γ ⊢ M⁻ ⇓ (nf M)⁻ : A  and Γ ⊢ N⁻ ⇓ (nf N)⁻ : A  
-- and the reduction is deterministic. by corrolary₂ we get M ≅ N
theorem₁₂ : ∀ {Γ A} t (M N : Γ ⊢ A)(red₁ : Γ ⊢ (M)⁻ ⇓ t ∶ A)(red₂ : Γ ⊢ (N)⁻ ⇓ t ∶ A) → Γ ⊢ A ∋ M ≅ N
theorem₁₂ t M N r₁ r₂ = {!!}

