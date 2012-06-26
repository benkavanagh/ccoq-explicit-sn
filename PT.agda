module PT where
-- Proof Trees  M N   contexts Γ etc.

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
import Relation.Binary.HeterogeneousEquality as H
import Level as Lvl

open import Closures
open import NatProperties


infixr 11 _⇒_
          
data Type : Set where
  ♭ : Type
  _⇒_ : (A B : Type) → Type

Name : Set
Name = ℕ

-- contexts and freshness constraints.

infix 10 _#_ [_∶_]∈_ _≥_
infix 11 _∙[_∶_]⊣_

mutual 

  data Context : Set where
    ε : Context
    _∙[_∶_]⊣_ : (Γ : Context) (x : Name) (A : Type) (f : T(x # Γ)) → Context

  _#_ : Name → Context → Bool
  x # ε = true
  x # (Γ ∙[ y ∶ A ]⊣ f) = (not ⌊ x ≟ y ⌋) ∧  (x # Γ)

max : Context → ℕ
max ε = 0
max (Γ ∙[ x ∶ A ]⊣ f) = max Γ ⊔ x

fresh : Context → ℕ
fresh = suc ∘ max

freshness : ∀ Γ {x} (pr : x > max Γ) → T (x # Γ)
freshness ε pr = tt
freshness (Γ ∙[ x ∶ A ]⊣ f) {y} pr with y ≟ x
freshness (Γ ∙[ x ∶ A ]⊣ f) {.x} pr | yes refl = <-irrefl (<≤-compat (s≤s (m≤n⊔m _ (max Γ))) pr)
... | no ¬p = freshness Γ (≤-trans (s≤s (m≤m⊔n _ _)) pr)

isfresh : ∀ Γ → T (fresh Γ # Γ)
isfresh Γ = freshness Γ (≤-refl _)



-- Occur 
-- Guillaume moves ':' to the right to parameterize datatype on commonly occuring elements 
-- of context to avoid replication of implicit quantification in all constructors. 

data [_∶_]∈_ (x : Name) (A : Type) : Context  → Set  where
  here! : ∀ {Γ} {f : T(x # Γ)} → [ x ∶ A ]∈ (Γ ∙[ x ∶ A ]⊣ f)
  there : ∀ {y B Γ} (f : T(y # Γ)) (occ : [ x ∶ A ]∈ Γ) → [ x ∶ A ]∈ Γ ∙[ y ∶ B ]⊣ f

data _≥_ (Δ : Context) : Context → Set  where
  stop :  Δ ≥ ε
  step : ∀ {Γ x A} (c : Δ ≥ Γ) (occ : [ x ∶ A ]∈ Δ) (f : T(x # Γ)) → Δ ≥ Γ ∙[ x ∶ A ]⊣ f  




-- prove the following lemmas from page 64
-- need monotonicity of occ (just by using occ¹)
lemma₁ : ∀{Δ Γ} (h : ∀{x A} → [ x ∶ A ]∈ Δ →  ([ x ∶ A ]∈ Γ)) → Γ ≥ Δ
lemma₁ {ε} h = stop
lemma₁ {Δ ∙[ x ∶ A ]⊣ f} h = step (lemma₁ {Δ} (\oc →  h (there f oc)))    -- Γ ≥ Δ
                                                    (h here!)
                                                    f 

lemma₂ : ∀ {Γ Δ} (c : Γ ≥ Δ) → ∀{x A} (occ : [ x ∶ A ]∈ Δ) → ([ x ∶ A ]∈ Γ)
lemma₂ stop ()
lemma₂ (step c occ f) here! = occ
lemma₂ (step c occ₁ f) (there .f occ₂) = lemma₂ c occ₂

lemma₃  : {Γ : Context} → Γ ≥ Γ 
lemma₃ = lemma₁ (λ z → z)

lemma₄ : {Θ Γ Δ : Context} → (Θ ≥ Γ) → (Γ ≥ Δ) → Θ ≥ Δ
lemma₄ h1 h2 = lemma₁ ((lemma₂ h1) ∘ (lemma₂ h2))


lemma₅ : ∀ {Γ x A}{f : T(x # Γ)} → (Γ ∙[ x ∶ A ]⊣ f) ≥ Γ
lemma₅  = lemma₁ (λ z → there _ z)



≟-diag : ∀ n → (n ≟ n) ≡ yes refl
≟-diag zero = refl
  -- here we compute [≟-diag n] in the same so that the [n ≟ n] inside
  -- reduces properly to the same result as [n ≟ n]
≟-diag (suc n) with n ≟ n | ≟-diag n    -- subproblems and facts we know about the subproblem.
... | .(yes refl) | refl = refl

{---------
Then you have to cases:

 ∙ either [p = occ⁰] which means that the context has the shape
   [Γ ⊎ x :: _ ⊣ f]  where [f] is a proof of
   [T (not(⌊ x ≟ x ⌋) ∧ whatever)].
   But [x ≟ x] is always true so this [f] is in fact a proof of
   False (an inhabitant of the empty set; see Data.Empty).

 ∙ or [p = occ¹ p f'] meaning that the context has the shape
   [Γ ⊎ y :: _ ⊣ f']. What prevents us from using [f] in the
   induction hypothesis is the [not (⌊ x ≟ y ⌋)] part so...
   we compute it away!
---------}

refuteFresh : ∀ {x Γ} {A} (f : T(x # Γ)) (p : [ x ∶ A ]∈ Γ) → ⊥
refuteFresh {x} f here! rewrite ≟-diag x = f 
refuteFresh {x} f (there {y} f' p)  with x ≟ y
... | yes pr = f
... | no ¬pr = refuteFresh f p


lemma₆ : ∀ {Γ x A } (h1 h2 : [ x ∶ A ]∈ Γ) → h1 ≡ h2
lemma₆ here! here! = refl
lemma₆ here! (there f h₂) = ⊥-elim (refuteFresh f h₂)  -- f says x # Γ.  h₂ says x in Γ
lemma₆ (there f h₁) (here!) = ⊥-elim (refuteFresh f h₁)  -- same as above.
lemma₆ (there f h₁) (there .f h₂) = cong (λ z → there f z) (lemma₆ h₁ h₂)

lemma₇ : {Γ Δ : Context} → (gt1 : Γ ≥ Δ) → (gt2 : Γ ≥ Δ) → gt1 ≡ gt2
lemma₇ stop stop = refl
lemma₇ (step g₁ occ₁ f) (step g₂ occ₂ .f ) = cong₂ (λ g occ → step g occ f) (lemma₇ g₁ g₂) (lemma₆ occ₁ occ₂)

≥-isPreorder : IsPreorder _≡_ _≥_
≥-isPreorder =
  record {
    isEquivalence = isEquivalence;
    reflexive = λ { {Γ} {.Γ} refl → lemma₃ };
    trans = lemma₄
  }

infix 10 _⊢_ _⇛_ 
infix 11  π_ _⊙_ _[_↦_]

-- M,N ::=  [Γ ∋ x ↳ loc] |  ∶λ x ⇨ M  |  M ⋆ N  |  M ⟨ σ ⟩
mutual 
  data _⊢_ : (Γ : Context)(A : Type) → Set where
    [_∋_↳_] : ∀ {A} Γ (x : Name) (occ :  [ x ∶ A ]∈ Γ) → Γ ⊢ A    -- var at occ location
    ∶λ_#_⇨_ : ∀{Γ A B} (x : Name)  (f : T(x # Γ)) (M : Γ ∙[ x ∶ A ]⊣ f ⊢ B) → Γ ⊢ A ⇒ B   -- lambda
    _⋆_ : ∀{Γ A B} (M : Γ ⊢ A ⇒ B) (N : Γ ⊢ A) → Γ ⊢ B          -- apply
    _⟨_⟩ : ∀{Δ}{Γ}{A} (M : Γ ⊢ A) (γ : Δ ⇛ Γ) → (Δ ⊢ A)   -- explicit subst

-- γ, δ ::= π c | γ ⊙ δ | γ [ x → M ]
  data _⇛_ : (Γ : Context)(Δ : Context) → Set where
    π_ : ∀{Δ}{Γ} (c : Δ ≥ Γ) → (Δ ⇛ Γ)      -- project
    _⊙_ :  ∀{Θ}{Γ}{Δ} (γ : Γ ⇛ Δ) (δ : Θ ⇛ Γ) → (Θ ⇛ Δ)    -- compose
    _[_↦_] : ∀{Δ}{Γ}{A} (γ : Δ ⇛ Γ) (x : Name) {f : T(x # Γ)} (M : Δ ⊢ A) → (Δ ⇛ (Γ ∙[ x ∶ A ]⊣ f))  -- update

infix 10 _⊢_∋_≐_ _⊢_∋_≐ˢ_

mutual

-- _⊢_∋_≐_   -->*   _⊢_∋_≅_    
  data _⊢_∋_≐_ : ∀ Γ A  (M N : Γ ⊢ A) → Set where
    cλ : ∀ {Γ x f A B M N} (r : Γ ∙[ x ∶ A ]⊣ f ⊢ B ∋ M ≐ N) → Γ ⊢ A ⇒ B ∋ ∶λ x # f ⇨ M ≐ ∶λ x # f ⇨ N
    ca₁ : ∀ {Γ A B M N P} (r : Γ ⊢ A ⇒ B ∋ M ≐ N) → Γ ⊢ B ∋ M ⋆ P ≐ N ⋆ P
    ca₂ : ∀ {Γ A B M P Q} (r : Γ ⊢ A ∋ P ≐ Q) → Γ ⊢ B ∋ M ⋆ P ≐ M ⋆ Q
    cs₁ : ∀ {Γ Δ A M N} {γ : Δ ⇛ Γ} (r : Γ ⊢ A ∋ M ≐ N) → Δ ⊢ A ∋ M ⟨ γ ⟩ ≐ N ⟨ γ ⟩
    cs₂ : ∀ {Γ Δ A M} {γ₁ γ₂ : Δ ⇛ Γ} (r : Δ ⊢ Γ ∋ γ₁ ≐ˢ γ₂) → Δ ⊢ A ∋ M ⟨ γ₁ ⟩ ≐ M ⟨ γ₂ ⟩
    :β : ∀{x Γ Δ}{f : T(x # Γ)} {γ : Δ ⇛ Γ} {A B}{M : (Γ ∙[ x ∶ A ]⊣ f)  ⊢ B}{N : Δ ⊢ A} →
         Δ ⊢ B ∋ (((∶λ x # f ⇨ M) ⟨ γ ⟩) ⋆ N) ≐ M ⟨ γ [ x ↦ N ] ⟩ 
    :η : ∀ {Γ A B x} {f : T(x # Γ)} (M : (Γ ⊢ (A ⇒ B))) { c } →
         Γ ⊢ A ⇒ B ∋ M  ≐ (∶λ x # f ⇨ ((M ⟨ π c ⟩) ⋆ [ (Γ ∙[ x ∶ A ]⊣ f) ∋ x ↳ here! ])) 
    :v₁ : ∀ {Γ Δ A x} {f : T(x # Γ)} {M γ} →
         Δ ⊢ A ∋ ([ (Γ ∙[ x ∶ A ]⊣ f) ∋ x ↳ here! ] ⟨ γ [ x  ↦ M ] ⟩) ≐  M
    :v₂ : ∀{Γ Δ : Context} {x A inΓ inΔ} {c : Δ ≥ Γ} →
          Δ ⊢ A ∋ ([ Γ ∋ x ↳ inΓ ] ⟨ π c ⟩) ≐  [ Δ ∋ x ↳ inΔ ] 
    :sid : ∀ {Γ A c M} → Γ ⊢ A ∋ M ⟨ π c ⟩ ≐ M 
    :sapp : ∀ {Γ Δ}{γ : Δ ⇛ Γ} {A B} {M : Γ ⊢ A ⇒ B}{N} →
            Δ ⊢ B ∋ (M ⋆ N) ⟨ γ ⟩ ≐  (M ⟨ γ ⟩ ⋆ N ⟨ γ ⟩)
    :s⊙ :  ∀{Θ Γ Δ A} {δ : Θ ⇛ Γ}{γ : Γ ⇛ Δ}{M : Δ ⊢ A} → Θ ⊢ A ∋ M ⟨ γ ⟩ ⟨ δ ⟩ ≐ M ⟨ γ ⊙ δ ⟩ 

-- _⊢_∋_≐ˢ_  -->*  _⊢_∋_≅ˢ_  
  data _⊢_∋_≐ˢ_ : ∀ Δ Γ  (γ δ : Δ ⇛ Γ) → Set where
    c∘₁ : ∀ {Ψ Δ Γ} {δ₁ δ₂ : Δ ⇛ Γ} {γ : Ψ ⇛ Δ} (r : Δ ⊢ Γ ∋ δ₁ ≐ˢ δ₂) → Ψ ⊢ Γ ∋ δ₁ ⊙ γ ≐ˢ δ₂ ⊙ γ
    c∘₂ : ∀ {Ψ Δ Γ} {δ : Δ ⇛ Γ} {γ₁ γ₂ : Ψ ⇛ Δ } (r : Ψ ⊢ Δ ∋ γ₁ ≐ˢ γ₂) → Ψ ⊢ Γ ∋ δ ⊙ γ₁ ≐ˢ δ ⊙ γ₂
    c≔₁ : ∀ {Δ Γ γ₁ γ₂ A x f M} (r : Δ ⊢ Γ ∋ γ₁ ≐ˢ γ₂) →
           Δ ⊢ Γ ∙[ x ∶ A ]⊣ f ∋  γ₁ [ x ↦ M ] ≐ˢ γ₂ [ x ↦ M ]
    c≔₂ : ∀ {Δ Γ γ A x f M N} (r : Δ ⊢ A ∋ M ≐ N) →
           Δ ⊢ Γ ∙[ x ∶ A ]⊣ f ∋ γ [ x ↦ M ] ≐ˢ γ [ x ↦ N ]
    ⊙-assoc : ∀ {Θ Δ Γ Ω}{γ : Γ ⇛ Ω}{δ : Δ ⇛ Γ}{θ : Θ ⇛ Δ } →
              Θ ⊢ Ω ∋ ((γ ⊙ δ) ⊙ θ) ≐ˢ (γ ⊙ (δ ⊙ θ))
    ∶ext∶⊙ : ∀ {Θ Δ Γ A } {γ : Δ ⇛ Γ} {x : Name} {δ : Θ ⇛ Δ} {f : T(x # Γ)} {M : Δ ⊢ A} →
            Θ ⊢ (Γ ∙[ x ∶ A ]⊣ f) ∋ (γ [ x ↦ M ] ⊙ δ) ≐ˢ ((γ ⊙ δ) [ x ↦ M ⟨ δ ⟩ ])
    ∶π∶ext : ∀ {Δ Γ A}{x : Name}{f : T(x # Γ)} {γ : Δ ⇛ Γ} {M : Δ ⊢ A}
             {c : (Γ ∙[ x ∶ A ]⊣ f) ≥ Γ } → Δ ⊢ Γ ∋ (π c ⊙ (γ [ x ↦ M ])) ≐ˢ  γ
    ∶⊙∶π  :  ∀ {Θ Δ Γ} {c₂ : Θ ≥ Δ} {c₁ : Δ ≥ Γ} {c₃ : Θ ≥ Γ} → Θ ⊢ Γ ∋ π c₁ ⊙ π c₂ ≐ˢ π c₃
    :πid :  ∀ {Δ Γ} {γ : Δ ⇛ Γ} {c : Δ ≥ Δ} → Δ ⊢ Γ ∋ (γ ⊙ π c) ≐ˢ γ
    :πε :  ∀ {Γ} {γ : Γ ⇛ ε} {c : Γ ≥ ε} → Γ ⊢ ε ∋ γ ≐ˢ (π c) 
    :ηε :  ∀ {Δ Γ A} (x : Name) {f : T(x # Γ)} (occ : [ x ∶ A ]∈ (Γ ∙[ x ∶ A ]⊣ f))
           (γ : Δ ⇛ (Γ ∙[ x ∶ A ]⊣ f)) (c : (Γ ∙[ x ∶ A ]⊣ f) ≥ Γ) →
           Δ ⊢ (Γ ∙[ x ∶ A ]⊣ f) ∋ γ  ≐ˢ ((π c ⊙ γ) [ x ↦ [(Γ ∙[ x ∶ A ]⊣ f) ∋ x ↳ occ ] ⟨ γ ⟩ ])

_⊢_∋_≅_ :  ∀ Γ A M N → Set
Γ ⊢ A ∋ M ≅ N = M ≡[ _⊢_∋_≐_ Γ A ]* N

_⊢_∋_≅ˢ_  : ∀ Γ Δ γ δ → Set
Γ ⊢ Δ ∋ γ ≅ˢ δ = γ ≡[ _⊢_∋_≐ˢ_ Γ Δ ]* δ


