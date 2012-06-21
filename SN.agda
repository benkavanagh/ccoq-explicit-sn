module SN where

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


-- Occur 
-- Guillaume moves ':' to the right to parameterize datatype on commonly occuring elements 
-- of context to avoid replication of implicit quantification in all constructors. 

data [_∶_]∈_ (x : Name) (A : Type) : Context  → Set  where
  here! : ∀ {Γ} {f : T(x # Γ)} → [ x ∶ A ]∈ (Γ ∙[ x ∶ A ]⊣ f)
  there : ∀ {y B Γ} (f : T(y # Γ)) (p : [ x ∶ A ]∈ Γ) → [ x ∶ A ]∈ Γ ∙[ y ∶ B ]⊣ f

data _≥_ (Γ : Context) : Context → Set  where
  stop :  Γ ≥ ε
  step : ∀ {Δ x A} (pr : Γ ≥ Δ) (occ : [ x ∶ A ]∈ Γ) (f : T(x # Δ)) → Γ ≥ Δ ∙[ x ∶ A ]⊣ f  



-- prove the following lemmas from page 64
-- need monotonicity of occ (just by using occ¹)
lemma₁ : ∀{Δ Γ} (h : ∀{x A} → [ x ∶ A ]∈ Δ →  ([ x ∶ A ]∈ Γ)) → Γ ≥ Δ
lemma₁ {ε} h = stop
lemma₁ {Δ ∙[ x ∶ A ]⊣ f} h = step (lemma₁ {Δ} (\oc →  h (there f oc)))    -- Γ ≥ Δ
                                                    (h here!)
                                                    f 

lemma₂ : ∀ {Γ Δ} (ge : Γ ≥ Δ) → ∀{x A} (pr : [ x ∶ A ]∈ Δ) → ([ x ∶ A ]∈ Γ)
lemma₂ stop ()
lemma₂ (step ge occ f) here! = occ
lemma₂ (step ge occ f) (there .f pr) = lemma₂ ge pr

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
    c∘₁ : ∀ {Γ Δ Ψ} {δ₁ δ₂} {γ : Ψ ⇛ Δ} (r : Δ ⊢ Γ ∋ δ₁ ≐ˢ δ₂) → Ψ ⊢ Γ ∋ δ₁ ⊙ γ ≐ˢ δ₂ ⊙ γ
    c∘₂ : ∀ {Γ Δ Ψ} {δ} {γ₁ γ₂} (r : Ψ ⊢ Γ ∋ γ₁ ≐ˢ γ₂) → Ψ ⊢ Δ ∋ δ ⊙ γ₁ ≐ˢ δ ⊙ γ₂
    c≔₁ : ∀ {Γ Δ γ₁ γ₂ A x f t} (r : Δ ⊢ Γ ∋ γ₁ ≐ˢ γ₂) →
           Δ ⊢ Γ ∙[ x ∶ A ]⊣ f ∋  γ₁ [ x ↦ t ] ≐ˢ γ₂ [ x ↦ t ]
    c≔₂ : ∀ {Γ Δ γ A x f t₁ t₂} (r : Δ ⊢ A ∋ t₁ ≐ t₂) →
           Δ ⊢ Γ ∙[ x ∶ A ]⊣ f ∋ γ [ x ↦ t₁ ] ≐ˢ γ [ x ↦ t₂ ]
    ⊙-assoc : ∀ {Γ Δ Θ Ω}{γ : Γ ⇛ Ω}{δ : Δ ⇛ Γ}{θ : Θ ⇛ Δ } →
              Θ ⊢ Ω ∋ ((γ ⊙ δ) ⊙ θ) ≐ˢ (γ ⊙ (δ ⊙ θ))
    ∶ext∶⊙ : ∀ {Γ A Δ Θ} {γ : Δ ⇛ Γ} {x : Name} {δ : Θ ⇛ Δ} {f : T(x # Γ)} {M : Δ ⊢ A} →
            Θ ⊢ (Γ ∙[ x ∶ A ]⊣ f) ∋ (γ [ x ↦ M ] ⊙ δ) ≐ˢ ((γ ⊙ δ) [ x ↦ M ⟨ δ ⟩ ])
    ∶π∶ext : ∀ {Γ Δ A}{x : Name}{f : T(x # Γ)} {γ : Δ ⇛ Γ} {M : Δ ⊢ A}
             {c : (Γ ∙[ x ∶ A ]⊣ f) ≥ Γ } → Δ ⊢ Γ ∋ (π c ⊙ (γ [ x ↦ M ])) ≐ˢ  γ
    ∶⊙∶π  :  ∀ {Θ Δ Γ} {c₂ : Θ ≥ Δ} {c₁ : Δ ≥ Γ} {c₃ : Θ ≥ Γ} → Θ ⊢ Γ ∋ π c₁ ⊙ π c₂ ≐ˢ π c₃
    :πid :  ∀ {Γ Δ} {γ : Γ ⇛ Δ} {c : Γ ≥ Γ} → Γ ⊢ Δ ∋ (γ ⊙ π c) ≐ˢ γ
    :πε :  ∀ {Γ} {γ : Γ ⇛ ε} {c : Γ ≥ ε} → Γ ⊢ ε ∋ γ ≐ˢ (π c) 
    :ηε :  ∀ {Γ Δ A} (x : Name) {f : T(x # Γ)} (occ : [ x ∶ A ]∈ (Γ ∙[ x ∶ A ]⊣ f))
           (γ : Δ ⇛ (Γ ∙[ x ∶ A ]⊣ f)) (c : (Γ ∙[ x ∶ A ]⊣ f) ≥ Γ) →
           Δ ⊢ (Γ ∙[ x ∶ A ]⊣ f) ∋ γ  ≐ˢ ((π c ⊙ γ) [ x ↦ [(Γ ∙[ x ∶ A ]⊣ f) ∋ x ↳ occ ] ⟨ γ ⟩ ])

_⊢_∋_≅_ :  ∀ Γ A M N → Set
Γ ⊢ A ∋ M ≅ N = M ≡[ _⊢_∋_≐_ Γ A ]* N

_⊢_∋_≅ˢ_  : ∀ Γ Δ γ δ → Set
Γ ⊢ Δ ∋ γ ≅ˢ δ = γ ≡[ _⊢_∋_≐ˢ_ Γ Δ ]* δ

-- semantic objects

-- first define Kripke models
record Kripke {a} : Set (Lvl.suc a) where
   constructor kripke
   field 
     W : Set a
     _≥ʷ_ : Rel W a   -- preorder rel
     isPO : IsPreorder (_≡_ {a} {W})  _≥ʷ_
     uniq≥ : {w₁ w₂ : W}(c₁ c₂ : w₁ ≥ʷ w₂) → c₁ ≡ c₂
     G : W → Set      -- Gw w₁ = interpretation of ⊙ at w₁


--  naturally one might try to use a datatype.
--  data  _⊩_  : (w : W) (A : Type) → Set where
--   Ground : ∀{w : W} → (f : (w' : W ) (c : w' ≥ʷ w) → (G w')) → w ⊩ ♭ 
--   Lambda : ∀{w : W}{A}{B} (f : (w' : W) (c : w' ≥ʷ w) (fc : w' ⊩ A) → (w' ⊩ B))  → w ⊩ (A ⇒ B)
--
--  This doesn't work because of positivity requirements on the datatype. 
--  Instead, as we did with NBE in agda course we define the model by recursion on the type rather than
--  as an inductive type. Using this method there is no positivity problem.


module KSem (K : Kripke )  where 
  open Kripke K
  module P = IsPreorder isPO         -- adds fields of isPO to namespace of module

  infix 10 _⊩_

  -- semantic objects
  _⊩_ : (w : W)(A : Type) → Set
  w ⊩ ♭ = {w' : W}(ge : w' ≥ʷ w) → G w'
  w ⊩ (A ⇒ B) = {w' : W} (ge : w' ≥ʷ w) (h : w' ⊩ A) → w' ⊩ B 

-- elimination rules for witnesses of forcing.... These give witnesses at future worlds.
-- TODO: give these appropriate infix syntax so there use below in Eq, Uni is apparent.
  ground-v : ∀{w' w} → (f : w ⊩ ♭) (ge : w' ≥ʷ w) → G w'
  ground-v f ge = f ge

  app-v : ∀{w' A w B}(u : w ⊩ (A ⇒ B)) (c : w' ≥ʷ w) (v : w' ⊩ A) → (w' ⊩ B)
  app-v u c v = u c v 

  ↑[_,_]⟨_⟩  : ∀ {w w'} (c : w' ≥ʷ w) A (u : w ⊩ A) → w' ⊩ A
  ↑[ c , ♭ ]⟨ u ⟩ = λ c' → u (P.trans c' c)
  ↑[ c , A ⇒ B ]⟨ u ⟩ = λ c' → u (P.trans c' c)


  mutual

    -- Equality (Eq)  and Uniformity (Uni) of semantic objects/values.
   
    -- Eq and Uni are mutually defined, binary and unary predicates over semantic objects u, v ∈ w ⊩ A
   
    -- Eq: two semantic objects at ground type are equal if they give the same element at all future worlds,
    --   and at function type if under application they map all uniform semantic objects to equal semantic objects               
    --          i.e. they are extensionally equal. 
    Eq⟨_⊩_⟩[_,_] : ∀ w A (u v : w ⊩ A) → Set
    Eq⟨ w ⊩ ♭ ⟩[ u , v ] = ∀ {w'} (c : w' ≥ʷ w) → u c ≡ v c
    Eq⟨ w ⊩ A ⇒ B ⟩[ u₁ , u₂ ] =
      ∀ {w'} (c : w' ≥ʷ w) {v : w' ⊩ A} (uni : Uni⟨ w' ⊩ A ⟩ v) → Eq⟨ w' ⊩ B ⟩[ u₁ c v , u₂ c v ]

    -- Uni: all ground semantic objects are uniform
    -- a semantic object of functional type is uniform 
    --   (1) maps uniform input objects to uniform output objects.
    --   (2) maps equal, uniform objects to equal output objects.
    --   (3) application and monotonicity commute. 
    Uni⟨_⊩_⟩_ : ∀ w A (u : w ⊩ A) → Set
    Uni⟨ w ⊩ ♭ ⟩ u = ⊤
    Uni⟨ w ⊩ A ⇒ B ⟩ u =
      (∀ {w'} (c : w' ≥ʷ w) {v} (uni : Uni⟨ w' ⊩ A ⟩ v) → Uni⟨ w' ⊩ B ⟩ u c v) ×
      (∀ {w'} (c : w' ≥ʷ w) {v₁ v₂} (uni₁ : Uni⟨ w' ⊩ A ⟩ v₁) (uni₂ : Uni⟨ w' ⊩ A ⟩ v₂)
         (eq : Eq⟨ w' ⊩ A ⟩[ v₁ , v₂ ]) → Eq⟨ w' ⊩ B ⟩[ u c v₁ , u c v₂ ]) ×
      (∀ {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) {v} (uni : Uni⟨ w₁ ⊩ A ⟩ v) →
        Eq⟨ w₂ ⊩ B ⟩[ ↑[ c₂ , B ]⟨ u c₁ v ⟩ , u c₃ (↑[ c₂ , A ]⟨ v ⟩) ])


  -- Eq is an equivalence 
  Eq-refl : ∀ A {w} (u : w ⊩ A) → Eq⟨ w ⊩ A ⟩[ u , u ]
  Eq-refl ♭ u = λ _ → refl
  Eq-refl (A ⇒ B) u = λ c v → Eq-refl B _    

  Eq-sym : ∀ A {w t u} (eq : Eq⟨ w ⊩ A ⟩[ t , u ]) → Eq⟨ w ⊩ A ⟩[ u , t ]
  Eq-sym ♭ eq = sym ∘ eq 
  Eq-sym (A ⇒ B) eq = λ c u → Eq-sym B ((eq c u))

  Eq-trans : ∀ A {w s t u} (eq₁ : Eq⟨ w ⊩ A ⟩[ s , t ]) (eq₂ : Eq⟨ w ⊩ A ⟩[ t , u ]) →
             Eq⟨ w ⊩ A ⟩[ s , u ]
  Eq-trans ♭ eq₁ eq₂ = λ c → trans (eq₁ c) (eq₂ c) 
  Eq-trans (S ⇒ T) eq₁ eq₂ = λ c u → Eq-trans T (eq₁ c u) (eq₂ c u)


  -- "equal uniform values can be substituted in app"
  -- Without uniformity this lemma requires extensionality. But if values uniform no problem.
  -- By uni₁ I can get Eq B u c v, u c v'      u' c v'  
  -- by eq1 I can bet Eq B u c v'  u' c v'
  -- by trans I can get Eq B u c v, u' c v'
  Eq-cong-app : ∀ {A B w w'} (c : w' ≥ʷ w) {u u' : w ⊩ A ⇒ B} {v v' : w' ⊩ A}
                (uni₁ : Uni⟨ w ⊩ A ⇒ B ⟩ u) (uni₁' : Uni⟨ w ⊩ A ⇒ B ⟩ u') (uni₂ : Uni⟨ w' ⊩ A ⟩ v) (uni₁ : Uni⟨ w' ⊩ A ⟩ v')
                (eq₁ : Eq⟨ w ⊩ A ⇒ B ⟩[ u , u' ]) (eq₂ : Eq⟨ w' ⊩ A ⟩[ v , v' ]) →
                Eq⟨ w' ⊩ B ⟩[ u c v , u' c v' ]   -- u c v = app u v ,   u' c v' = app u' v'
  Eq-cong-app {A} {B} {w} {w'} c uni₁ uni₁' uni₂ uni₂' eq₁ eq₂ = 
              Eq-trans B {w'} ((Σ.proj₁ (Σ.proj₂ uni₁)) c uni₂ uni₂'  eq₂) (eq₁ c uni₂') 


  --  "↑  gives equal results for equal input"
  Eq-cong-↑ : ∀ A {w w'} (c : w' ≥ʷ w) {s t} (eq : Eq⟨ w ⊩ A ⟩[ s , t ]) →
             Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]⟨ s ⟩ , ↑[ c , A ]⟨ t ⟩ ]
  Eq-cong-↑ ♭ c eq = λ c' → eq _
  Eq-cong-↑ (A ⇒ B) c eq = λ c' {v} uni → eq _ uni

   -- "↑ gives uniform output for uniform input"
  ↑Uni-endo : ∀ A {w w' : W} (c : w' ≥ʷ w) u (uni : Uni⟨ w ⊩ A ⟩ u) → Uni⟨ w' ⊩ A ⟩ (↑[ c , A ]⟨ u ⟩)
  ↑Uni-endo ♭ {w}{w'} c u uni = tt
  ↑Uni-endo (A ⇒ B) {w} {w'} c u uni = 
            ( (λ c' univ → ((Σ.proj₁ uni) (P.trans c' c) univ)) ,
             ( (λ c' uni₂ uni₂' eq → (Σ.proj₁ (Σ.proj₂ uni)) (P.trans c' c) uni₂ uni₂' eq) ,
              (λ c₁ c₂ c₃ uni₂ → (Σ.proj₂ (Σ.proj₂ uni)) (P.trans c₁ c) c₂ (P.trans c₃ c) uni₂) )) 

  -- 
  Eq↑ : ∀ A {w} u (c : w ≥ʷ w) → Eq⟨ w ⊩ A ⟩[ ↑[ c , A ]⟨ u ⟩ , u ]
  Eq↑ ♭ u c = λ c' → cong u (uniq≥ _ _)
  Eq↑ (A ⇒ B) {w} u c = f   
     where 
       f :  {w' : W} (c' : w' ≥ʷ w) {v : w' ⊩ A} → Uni⟨ w' ⊩ A ⟩ v → Eq⟨ w' ⊩ B ⟩[ ↑[ c , A ⇒ B ]⟨ u ⟩ c' v , u c' v ]
       f c' u' rewrite (uniq≥ (P.trans c' c) c') = Eq-refl B _


{-  Method using subst by G.Allais.  subst allows you to substitute values of ≡ type.   
  Eq↑ : ∀ A {w} u (c : w ≥ʷ w) → Eq⟨ w ⊩ A ⟩[ ↑[ c , A ]⟨ u ⟩ , u ]
  Eq↑ ♭ u c = λ c' → cong u (uniq≥ _ c')
  Eq↑ (A ⇒ B) u c =
  -- cast
    λ {w'} c' {v} uni' → subst (λ c → Eq⟨ w' ⊩ B ⟩[ u c v , u c' v ]) (uniq≥ c' _)
  -- actual proof
    (Eq-refl B (u c' v))
-}
  
  Eq↑↑ : ∀ A {w} u {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) →
         Eq⟨ w₂ ⊩ A ⟩[ ↑[ c₂ , A ]⟨ ↑[ c₁ , A ]⟨ u ⟩ ⟩ , ↑[ c₃ , A ]⟨ u ⟩ ]
  Eq↑↑ ♭ u c₁ c₂ c₃ = λ c → cong u (uniq≥ _ _)
  Eq↑↑ (A ⇒ B) {w} u {w₁} {w₂} c₁ c₂ c₃ = f
    where 
      f : ∀ {w' : W} (c : w' ≥ʷ w₂) {v : w' ⊩ A} → Uni⟨ w' ⊩ A ⟩ v → Eq⟨ w' ⊩ B ⟩[ ↑[ c₂ , A ⇒ B ]⟨ ↑[ c₁ , A ⇒ B ]⟨ u ⟩ ⟩ c v ,
                                                                                                                   ↑[ c₃ , A ⇒ B ]⟨ u ⟩ c v ] 
      f c u rewrite (uniq≥ (P.trans (P.trans c c₂) c₁) (P.trans c c₃)) = Eq-refl B _

{- subst version.
  Eq↑↑ : ∀ A {w} u {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) →
         Eq⟨ w₂ ⊩ A ⟩[ ↑[ c₂ , A ]⟨ ↑[ c₁ , A ]⟨ u ⟩ ⟩ , ↑[ c₃ , A ]⟨ u ⟩ ]
  Eq↑↑ ♭ u c₁ c₂ c₃ = λ c → cong u (uniq≥ _ _)
  Eq↑↑ (A ⇒ B) u c₁ c₂ c₃ = 
  -- cast
    λ {w'} c' {v} uni' → subst (λ c → Eq⟨ w' ⊩ B ⟩[ u c v , u (P.trans c' c₃) v ]) (uniq≥ _ _)
  -- actual proof
    (Eq-refl B (u _ v))
-}

  Eqapp↑ : ∀ {w B A} (u : w ⊩ A ⇒ B) {w'} (c : w' ≥ʷ w) {v} →
           Eq⟨ w' ⊩ B ⟩[ u c v , (↑[ c , A ⇒ B ]⟨ u ⟩) P.refl v ]
  Eqapp↑ {w} {B} u {w'} c {v} rewrite (uniq≥ (P.trans P.refl c) c) = Eq-refl B _ 

{- subst version.
  Eqapp↑ : ∀ {w B A} (u : w ⊩ A ⇒ B) {w'} (c : w' ≥ʷ w) {v} →
           Eq⟨ w' ⊩ B ⟩[ u c v , (↑[ c , A ⇒ B ]⟨ u ⟩) P.refl v ]
  Eqapp↑ {w} {B} u {w'} c {v} =
    subst (λ c' → Eq⟨ w' ⊩ B ⟩[ u c v , u c' v ]) (uniq≥ _ _) (Eq-refl B (u c v))
-}

-- advantages, subst requires to explicitly label rewrite sites, but allows precise 
-- expression of context. 
-- rewrite applies rewrite everywhere in goal expression. 
-- ergo....  subst is more precise.    


-- semantic environments
-- Two options for definition
--    1. datatype. 
--    2. definition of set over contexts.
--  
  -- _⊩ᵉ_  = semantic environments (tuples of values)
  -- ↑̂ᵉ[ c , Γ ]⟨ ρ ⟩   = lifting / coercion / weakening of environment ρ from Δ ⊩ᵉ Γ to Θ ⊩ᵉ Γ if c : Θ ≥ Γ 
  -- πᵉ c ρ  = ↓ᵉ[ c ] ⟨ ρ ⟩ =  semantic projection from Δ ⊩ᵉ Γ  to  Δ ⊩ᵉ Θ if  c : Γ ≥ Θ
  --                                      here we diverge from notation in paper. prefer to keep π as projection.

  -- emacs unicode note: 
  -- To get  ᵉ superscript need to add 
  --  (custom-set-variables '(agda-input-user-translations (quote (("^e" "ᵉ")))))
  -- to .emacs file 

  infix 10 _⊩ᵉ_ ↑ᵉ[_,_]⟨_⟩

  _⊩ᵉ_ : ∀ (w : W) (Γ : Context) → Set
  w ⊩ᵉ ε = ⊤
  w ⊩ᵉ Γ ∙[ x ∶ A ]⊣ f = w ⊩ᵉ Γ × w ⊩ A

  lookup : ∀ {w} Γ (ρ : w ⊩ᵉ Γ) {x A} (occ : [ x ∶ A ]∈ Γ) → w ⊩ A
  lookup ε _ () 
  lookup ._ (_ , t) (here!) = t
  lookup ._ (ρ , _) (there f occ) = lookup _ ρ occ

  ↑ᵉ[_,_]⟨_⟩ : ∀ {w w'} (c : w' ≥ʷ w) Γ (ρ : w ⊩ᵉ Γ) → w' ⊩ᵉ Γ
  ↑ᵉ[ c , ε ]⟨ ρ ⟩ = ρ
  ↑ᵉ[ c , Γ ∙[ x ∶ A ]⊣ f ]⟨ ρ , t ⟩ = ↑ᵉ[ c , Γ ]⟨ ρ ⟩ , ↑[ c , A ]⟨ t ⟩

  -- need projection for semantic environments to mirror projection in explicit substitutions.
  -- in the paper this is written ↓c
  -- problem is the confusion between empty context/env and  'sign' for environment. would love ̂ρ
  πᵉ : ∀ {w Γ Δ} (c : Γ ≥ Δ) (ρ : w ⊩ᵉ Γ) → w ⊩ᵉ Δ
  πᵉ stop ρ = tt
  πᵉ (step c occ f) ρ = πᵉ c ρ , lookup _ ρ occ

  -- equality of semantic environments.
  Eq⟨_⊩ᵉ_⟩[_,_] : ∀ w Γ (ρ₁ ρ₂ : w ⊩ᵉ Γ) → Set
  Eq⟨ w ⊩ᵉ ε ⟩[ ρ₁ , ρ₂ ] = ⊤
  Eq⟨ w ⊩ᵉ Γ ∙[ x ∶ A ]⊣ f ⟩[ (ρ₁ , r₁) , (ρ₂ , r₂) ] = Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ] × Eq⟨ w ⊩ A ⟩[ r₁ , r₂ ]
 
  -- uniformity of semantic environments
  Uni⟨_⊩ᵉ_⟩_ : ∀ w Γ (ρ : w ⊩ᵉ Γ) → Set
  Uni⟨ w ⊩ᵉ ε ⟩ ρ = ⊤
  Uni⟨ w ⊩ᵉ Γ ∙[ x ∶ A ]⊣ f ⟩ (ρ , r) = Uni⟨ w ⊩ᵉ Γ ⟩ ρ × Uni⟨ w ⊩ A ⟩ r

  -- Eq⟨ w ⊩ᵉ Γ ⟩[_, _]  is an equivalence.
  Eqᵉ-refl : ∀ {w} Γ ρ → Eq⟨ w ⊩ᵉ Γ ⟩[ ρ , ρ ]
  Eqᵉ-refl ε ρ = tt
  Eqᵉ-refl (Γ ∙[ x ∶ A ]⊣ f) (ρ , r) = Eqᵉ-refl Γ ρ , Eq-refl A r

  Eqᵉ-sym : ∀ Γ {w ρ₁ ρ₂} (eq : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ]) → Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₂ , ρ₁ ]
  Eqᵉ-sym ε eq = tt


  Eqᵉ-sym (Γ ∙[ x ∶ A ]⊣ f) (eqρ , eqr) = Eqᵉ-sym Γ eqρ , Eq-sym A eqr

  Eqᵉ-trans : ∀ Γ {w ρ₁ ρ₂ ρ₃} (eq₁ : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ]) (eq₂ : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₂ , ρ₃ ]) →
             Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₃ ]
  Eqᵉ-trans ε eq₁ eq₂ = tt
  Eqᵉ-trans (Γ ∙[ x ∶ A ]⊣ f) (eqρ₁ , eqr₁) (eqρ₂ , eqr₂) = Eqᵉ-trans Γ eqρ₁ eqρ₂ , Eq-trans A eqr₁ eqr₂

  -- lookup is invariant of witness of occurrence since witnesses are unique (lemma₆)
  lookup-uniq : ∀ {Γ w} ρ {A x} (pr₁ pr₂ : [ x ∶ A ]∈ Γ) →
                Eq⟨ w ⊩ A ⟩[ lookup Γ ρ pr₁ , lookup Γ ρ pr₂ ]
  lookup-uniq {Γ} ρ {A} pr₁ pr₂ rewrite lemma₆ pr₁ pr₂ = Eq-refl A (lookup Γ ρ pr₂)

  -- lookup is invariant on projection operation
  Eq-lookup : ∀ {Γ Δ w ρ} (ge : Γ ≥ Δ) {x A} (pr : [ x ∶ A ]∈ Γ) (pr' : [ x ∶ A ]∈ Δ) →
              Eq⟨ w ⊩ A ⟩[ lookup Γ ρ pr , lookup Δ (πᵉ ge ρ) pr' ]
  Eq-lookup stop pr ()
  Eq-lookup {Γ} {._} {w} {ρ} (step ge occ f) {x} {A} pr here! = lookup-uniq ρ pr occ
  Eq-lookup (step ge occ f) pr (there .f pr') = Eq-lookup ge pr pr' 

  -- lifting/weakening and lookup are commuting / coherent operations
  Eq↑-lookup : ∀ {Γ w w'} (c : w' ≥ʷ w) ρ {x A} (pr : [ x ∶ A ]∈ Γ) →
               Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]⟨ lookup Γ ρ pr ⟩ , lookup Γ ↑ᵉ[ c , Γ ]⟨ ρ ⟩ pr ]
  Eq↑-lookup {ε} c ρ ()
  Eq↑-lookup {Γ ∙[ x ∶ A ]⊣ f} c (_ , r) here! = Eq-refl A ↑[ c , A ]⟨ r ⟩
  Eq↑-lookup c (ρ , _) (there f pr) = Eq↑-lookup c ρ pr

  -- projection from Γ semantic env to Δ semantic env gives same result
  -- as projection from Γ extended with fresh variable x, since obviously x cannot 
  -- be in Δ (hence refuteFresh case)
  Eqπ-step : ∀ {w Γ ρ Δ} (c₁ : Γ ≥ Δ) {x A v f} (c₂ : Γ ∙[ x ∶ A ]⊣ f ≥ Δ) →
             Eq⟨ w ⊩ᵉ Δ ⟩[ πᵉ c₂ (ρ , v) , πᵉ c₁ ρ ]
  Eqπ-step stop c₂ = tt
  Eqπ-step (step c₁ occ f) (step c₂ (here! {_} {g}) .f) = ⊥-elim (refuteFresh g occ)
  Eqπ-step (step c₁ occ f) (step c₂ (there f₁ occ₁) .f) =
    Eqπ-step c₁ c₂ , Eq-lookup (step c₁ occ f) occ₁ here!

  -- Sem env ρ is equal to identity (c : Γ ≥ Γ) restriction on ρ.
  Eqπ : ∀ Γ {w ρ} (c : Γ ≥ Γ) → Eq⟨ w ⊩ᵉ Γ ⟩[ πᵉ c ρ , ρ ]
  Eqπ ε stop = tt
  Eqπ (Γ ∙[ x ∶ A ]⊣ f) (step c here! .f) =
    Eqᵉ-trans Γ (Eqπ-step lemma₃ c) (Eqπ Γ _) , Eq-refl A _
  Eqπ (Γ ∙[ x ∶ A ]⊣ f) (step c (there .f occ) .f) = ⊥-elim (refuteFresh f occ)

  -- Sem env ρ is equal to ρ lifted by identity on world c : w ≥ʷ w
  Eqᵉ↑ : ∀ Γ {w ρ} (c : w ≥ʷ w) → Eq⟨ w ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ρ ⟩ , ρ ]
  Eqᵉ↑ ε c = tt
  Eqᵉ↑ (Γ ∙[ x ∶ A ]⊣ f) c = Eqᵉ↑ Γ c , Eq↑ A _ c

  -- multiple projections equal to projection by composed ordering (by trans)
  Eqππ : ∀ Γ Δ Ε {w} {ρ : w ⊩ᵉ Ε} (ge₁ : Δ ≥ Γ) (ge₂ : Ε ≥ Δ) (ge₃ : Ε ≥ Γ) →
         Eq⟨ w ⊩ᵉ Γ ⟩[ πᵉ ge₁ (πᵉ ge₂ ρ) , πᵉ ge₃ ρ ]
  Eqππ .ε Δ Ε stop ge₂ ge₃ = tt
  Eqππ (Γ ∙[ x ∶ A ]⊣ f) Δ Ε (step ge₁ occ .f) ge₂ ge₃
    rewrite lemma₇ ge₃ (lemma₄ ge₂ (step ge₁ occ f)) =
    Eqππ Γ Δ Ε ge₁ ge₂ _ , Eq-sym A (Eq-lookup ge₂ (lemma₂ ge₂ occ) occ)

  -- multiple liftings equivalent to lifting by composed ordering (by trans)
  Eqᵉ↑↑ : ∀ Γ {w w₁ w₂} {ρ : w ⊩ᵉ Γ} (c₂ : w₂ ≥ʷ w₁) (c₁ : w₁ ≥ʷ w) (c₃ : w₂ ≥ʷ w) →
          Eq⟨ w₂ ⊩ᵉ Γ ⟩[ ↑ᵉ[ c₂ , Γ ]⟨ ↑ᵉ[ c₁ , Γ ]⟨ ρ ⟩ ⟩ , ↑ᵉ[ c₃ , Γ ]⟨ ρ ⟩ ]
  Eqᵉ↑↑ ε c₁ c₂ c₃ = tt
  Eqᵉ↑↑ (Γ ∙[ x ∶ A ]⊣ f) c₁ c₂ c₃ = (Eqᵉ↑↑ Γ c₁ c₂ c₃) , (Eq↑↑ A _ c₂ c₁ c₃)

  Eqᵉ↑π : ∀ {Γ} Δ {w} w' {ρ : w ⊩ᵉ Γ} (cw : w' ≥ʷ w) (cε : Γ ≥ Δ) →
          Eq⟨ w' ⊩ᵉ Δ ⟩[ ↑ᵉ[ cw , Δ ]⟨ πᵉ cε ρ ⟩ , πᵉ cε ↑ᵉ[ cw , Γ ]⟨ ρ ⟩ ]
  Eqᵉ↑π .ε w' cw stop = tt
  Eqᵉ↑π (Δ ∙[ x ∶ A ]⊣ f) w' {ρ} cw (step cε occ .f) = Eqᵉ↑π Δ w' cw cε , Eq↑-lookup cw ρ occ

-- semantics of the λ-calculus

  mutual

    ⟦_⟧t : ∀ {Γ w A} (M : Γ ⊢ A) (ρ : w ⊩ᵉ Γ) → w ⊩ A
    ⟦ [ Γ ∋ x ↳ p ] ⟧t ρ = lookup Γ ρ p
    ⟦_⟧t {Γ} (∶λ x # f ⇨ M) ρ = λ c a → ⟦ M ⟧t (↑ᵉ[ c , Γ ]⟨ ρ ⟩ , a)
    ⟦ M ⋆ N ⟧t ρ = ⟦ M ⟧t ρ P.refl (⟦ N ⟧t ρ)
    ⟦ M ⟨ γ ⟩ ⟧t ρ = ⟦ M ⟧t (⟦ γ ⟧s ρ)

    ⟦_⟧s : ∀ {w Γ Δ} (γ : Δ ⇛ Γ) (ρ : w ⊩ᵉ Δ) → w ⊩ᵉ Γ
    ⟦ π c ⟧s ρ = πᵉ c ρ
    ⟦ γ₂ ⊙ γ₁ ⟧s ρ = ⟦ γ₂ ⟧s (⟦ γ₁ ⟧s ρ)
    ⟦ γ [ x ↦ M ] ⟧s ρ = ⟦ γ ⟧s ρ , ⟦ M ⟧t ρ


  ----- Soundness of interpretation (this is true for any kripke model) (from pg 76)

  -- ⟦M⟧ρ and ⟦γ⟧ρ are uniform if ρ is uniform
  Uni-⟦⟧t : ∀ {Γ w A} (M : Γ ⊢ A) ρ (uni : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) → Uni⟨ w ⊩ A ⟩ (⟦ M ⟧t ρ)
  Uni-⟦⟧t M ρ uni = {!!}

  Uni-⟦⟧s : ∀{Δ w Γ} (γ : Δ ⇛ Γ) ρ (uni : Uni⟨ w ⊩ᵉ Δ ⟩ ρ) → Uni⟨ w ⊩ᵉ Γ ⟩ (⟦ γ ⟧s ρ)
  Uni-⟦⟧s γ ρ uni = {!!}


  -- Eq(⟦M⟧ρ₁,⟦M⟧ρ₂) and Eq(⟦γ⟧ρ₁,⟦γ⟧ρ₂), if Eq(ρ₁,ρ₂)
  Eq-⟦⟧t-compat : ∀ {Γ A w} {ρ₁ , ρ₂ : w ⊩ᵉ Γ} (M : Γ ⊢ A) (eq : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ])
                       → Eq⟨ w ⊩ A ⟩[ ⟦ M ⟧t ρ₁ , ⟦ M ⟧t ρ₂ ]
  Eq-⟦⟧t-compat = {!!}

  Eq-⟦⟧s-compat :  ∀ {Δ Γ w ρ₁ ρ₂} (γ : Δ ⇛ Γ)(eq : Eq⟨ w ⊩ᵉ Δ ⟩[ ρ₁ , ρ₂ ]) 
                       → Eq⟨ w ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s ρ₁ , ⟦ γ ⟧s ρ₂ ]
  Eq-⟦⟧s-compat = {!!}



  -- Eq(↑c(⟦M⟧ρ),⟦M⟧↑c(ρ)) and Eq(↑c(⟦γ⟧ρ),⟦γ⟧↑c(ρ))
  Eq-⟦M⟧↑-coherence : ∀ {Γ A}(M : Γ ⊢ A){w w'}(ρ : w ⊩ᵉ Γ)(c : w' ≥ʷ w)
                         → Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]⟨ ⟦ M ⟧t ρ ⟩ , ⟦ M ⟧t ↑ᵉ[ c , Γ ]⟨ ρ ⟩ ]
  Eq-⟦M⟧↑-coherence M ρ c = {!!}


  Eq-⟦γ⟧↑-coherence : ∀ {Δ Γ}(γ : Δ ⇛ Γ){w w'}(ρ : w ⊩ᵉ Δ)(c : w' ≥ʷ w)
                         → Eq⟨ w' ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ⟦ γ ⟧s ρ ⟩ , ⟦ γ ⟧s ↑ᵉ[ c , Δ ]⟨ ρ ⟩ ]
  Eq-⟦γ⟧↑-coherence γ ρ c = {!!}

  -- Theorem 4: M,N ∈ Γ ⊢ A; M≅N; ρ ∈ w ⊩ᵉ Γ → Eq(⟦M⟧ρ,⟦N⟧ρ)
  -- proof of both by induction on the proof of conversion.
  mutual 
    theorem₄ : ∀ {Γ A w} (M , N : Γ ⊢ A)(MN : Γ ⊢ A ∋ M ≅ N)(ρ : w ⊩ᵉ Γ) → Eq⟨ w ⊩ A ⟩[ ⟦ M ⟧t ρ , ⟦ N ⟧t ρ ]
    theorem₄ M N cv ρ = {!!}
 
    sound-subst : ∀ {Δ Γ w} (γ , δ : Δ ⇛ Γ)(γδ : Δ ⊢ Γ ∋ γ ≅ˢ δ)(ρ : w ⊩ᵉ Δ) → Eq⟨ w ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s ρ , ⟦ δ ⟧s ρ ]
    sound-subst γ δ cvε ρ = {!!}

--- End of module KSem   (Kripke semantics for terms)


calculus : Kripke
calculus = kripke Context _≥_ ≥-isPreorder lemma₇ (λ Γ → Γ ⊢ ♭)

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


module KS = KSem calculus
open KS

_⊢⇑_ : (Γ : Context)(A : Type) → Set
Γ ⊢⇑ A = ∀ {Δ} (c : Δ ≥ Γ) → Δ ⊢ A

mutual

  -- idea: 
  -- if M ∈ Γ ⊢ A₁ → ... → An → ♭  then
  -- reify (⟦M⟧) ≝ λ(z₁ : A₁)...λ(zn : An).(⟦M⟧ val(z₁)...val(zn)
  -- where ⟦M⟧ val(z₁)...val(zn) is a proof tree of type ♭ and z₁ ... zn are fresh names
  --  and if x is a variable of type A₁ → ...Ak → B, then
  --  val(x) = Λ([v₁]...Λ([vk](x reify(v₁) ... reify(vn))  (where [v₁] is simplified abstraction of (c, v) wher
  --       c is a world extension w' ≥ w, v is an element of w' ⊩ Ai
  -- Example: 
  --   M ∈ ε ⊢ ((♭ → ♭) → ♭) → (♭ → ♭) → ♭  = λ [x : ((♭ → ♭) → ♭)]. λ [y : (♭ → ♭)]. x ⋆ y
  --   reify(⟦M⟧) = λ(z₁ : (♭ → ♭) → ♭). λ(z₂ : ♭ → ♭). (⟦M⟧ val(z₁) val(z₂))
  --                   = λ(z₁ : (♭ → ♭) → ♭). λ(z₂ : ♭ → ♭). z₁ (λ (z₃ : ♭). (z₂ z₃)    : by (1)

  --  (1)  ⟦M⟧ val(z₁) val(z₂) = ⟦x y⟧{x = val(z₁), y = val(z₂)}
  --                                    = app(val(z₁), val(z₂))
  --                                    = app(Λ([v](z₁ reify(v))), val(z₂))
  --                                    = z₁ (reify (val(z₂)))    
  --                                    = z₁ (λ (z₃ : ♭). (z₂ z₃)      : by (2)
  --  (2)   reify (val(z₂)) has type ♭ → ♭ so
  --         reify (val(z₂)) = λ (z₃ : ♭). app(val(z₂), val(z₃))
  --                             = λ (z₃ : ♭). app(Λ([v](z₂ reify(v))),  z₃)
  --                             = λ (z₃ : ♭). (z₂ reify(z₃))
  --                             = λ (z₃ : ♭). (z₂ z₃)

  -- map value of term kripke model to well typed term.
  reify : ∀ Γ A (u : Γ ⊩ A) → Γ ⊢ A
  reify Γ ♭ u = u lemma₃
  reify Γ (A ⇒ B) u = ∶λ (fresh Γ) # (isfresh Γ)
                                  ⇨ (reify _ B (u lemma₅ (val _ A (λ {Δ} (pr : Δ ≥ _) → [ _ ∋ fresh Γ ↳ lemma₂ pr here! ]))))

  -- map upward-closed family of (well-typed) terms to value in kripke term model
  --   Intuitively val intuitively takes a variable and produces  proof tree of the form of a variable applied to zero or
  --   whose values will be reified semantic values.  
  --   Observations:
  --      1. these look a lot like neutral values. How can I make this more precise?
  --      2. this function looks very underspecified. These upward closed familes could be arbitrary but they almost 
  --          certainly are not. fix this.
  val : ∀ Γ A (f : Γ ⊢⇑ A) → Γ ⊩ A
  val Γ ♭ t = t
  val Γ (A ⇒ B) t = λ {Δ} pr a → val Δ B (λ {Ε} inc → t (lemma₄ inc pr) ⋆ (reify Ε A ↑[ inc , A ]⟨ a ⟩))

--- END OF mutual decl for reify/val


-- what does valEq below say? 
-- first thought, the type (t : ∀ {Δ} (pr : Δ ≥ Γ) → Δ ⊢ A) needs a name.  I will use 'upward closed familiy of terms' for now
-- Is this a family of proof trees 'above Γ' which designate the same term? 
-- essentially this is the idea, even if the straightforward constructive reading is different
-- i.e. for every environment Δ that contains Γ, a well typed term in Δ.

-- OK. two identical upward-closed family of terms yield identical kripke values. 
valEq : ∀ {Γ} A {f₁ f₂ : ∀ {Δ} (pr : Δ ≥ Γ) → Δ ⊢ A} (h : ∀ {Δ} (pr : Δ ≥ Γ) → f₁ pr ≡ f₂ pr) →
        Eq⟨ Γ ⊩ A ⟩[ val Γ A f₁ , val Γ A f₂ ]
valEq ♭ h = h
valEq (A ⇒ B) h =
  λ {Δ} pr {a} uni → valEq B (λ {Ε} inc → cong (λ t → t ⋆ reify Ε A ↑[ inc , A ]⟨ a ⟩)
    (h (lemma₁ (λ {x} {A₁} ext → lemma₂ inc (lemma₂ pr ext)))))


-- lifting result of val over contexts same as taking value at higher world 
--    (with appropriately constructed upward closed family of terms)
val↑ : ∀ {Γ} A {Δ} (pr : Δ ≥ Γ) {f : ∀ {Δ} (pr : Δ ≥ Γ) → Δ ⊢ A} →
       Eq⟨ Δ ⊩ A ⟩[ ↑[ pr , A ]⟨ val Γ A f ⟩ , val Δ A (λ {Ε} (inc : Ε ≥ Δ) → f (lemma₄ inc pr)) ]
val↑ ♭ pr = λ _ → refl
val↑ (A ⇒ B) pr {f} =
  λ {Δ} inc {a} uni → valEq B (λ {Ε} inc → cong (λ t → f t ⋆ reify Ε A ↑[ inc , A ]⟨ a ⟩)
  (lemma₇ _ _))

mutual

  -- Equal semantic values reify to elements in the same equivalence class of terms. 
  theorem₁ : ∀ {Γ} A {u v} (eq : Eq⟨ Γ ⊩ A ⟩[ u , v ]) → reify Γ A u ≡ reify Γ A v
  theorem₁ ♭ eq = eq _
  theorem₁ {Γ} (A ⇒ B) eq = cong (∶λ_#_⇨_ (fresh Γ)(isfresh Γ)) (theorem₁ B (eq lemma₅ (valUni A)))

  -- reflection/values of upward closed family of terms is a uniform value.   (What does this mean?)
  valUni : ∀ {Γ} A {f : ∀ {Δ} pr → Δ ⊢ A} → Uni⟨ Γ ⊩ A ⟩ val Γ A f
  valUni ♭ = tt
  valUni (A ⇒ B) {f} =
    (λ {Δ} inc {a} uni → valUni B) ,
    (λ {Δ} inc {v₁} {v₂} uni₁ uni₂ eq →
      valEq B (λ {Ε} pr → cong (_⋆_ (f (lemma₄ pr inc))) (theorem₁ A (Eq-cong-↑ A pr eq)))) ,
    (λ {Δ} {Ε} c₁ c₂ c₃ {v} uni → Eq-trans B (val↑ B c₂)
      (valEq B (λ {Φ} pr → cong₂ (λ inc t → f inc ⋆ t) (lemma₇ _ _)
               (theorem₁ A (Eq-sym A (Eq↑↑ A v _ _ _))))))

infix 10 idε_

-- default 'identity' term model environment
idε_ : (Γ : Context) → Γ ⊩ᵉ Γ
idε ε = tt
idε Γ ∙[ x ∶ A ]⊣ f =
  ↑ᵉ[ lemma₅ , Γ ]⟨ idε Γ ⟩ ,
  val _ A (λ {Δ} inc → [ Δ ∋ x ↳ lemma₂ inc here! ])

id↑ᵉ : ∀ {Γ Δ} (c : Δ ≥ Γ) → Δ ⊩ᵉ Γ
id↑ᵉ {Γ} {Δ} c = ↑ᵉ[ c , Γ ]⟨ idε Γ ⟩

-- normal form = reify ∘ eval
nf : ∀ {Γ A} (M : Γ ⊢ A) → Γ ⊢ A
nf {Γ} {A} M = reify Γ A (⟦ M ⟧t (idε Γ))

corollary₁ : ∀ {Γ A} {M N : Γ ⊢ A} (eq : Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idε Γ) , ⟦ N ⟧t (idε Γ) ]) → nf M ≡ nf N
corollary₁ eq = theorem₁ _ eq


-- *******  Completeness for equational theory.  i.e. proper completeness  *************
-- *********      Goal:  Eq(⟦M⟧idε, ⟦N⟧idε)  implies   M ≅ N                    ******************
-- use Kripke relation CV
-- 
-- [Γ, A] M ∿ u  ≡ M, u are CV-related at type A in context Γ    (equiv to tait computability predicate)
-- [Δ, Γ]ε γ ∿ ρ   ≡  γ, ρ are CV-related at env Γ in context Δ

infix 10 [_,_]_∿_  [_,_]ε_∿_

-- ∿ relates terms to values. 
-- t, T ∿-related at base/ground type if composition of t with proj subst π (c : Δ ≥ Γ) and T applied to 
--       c are convertible/equivalent terms
--       ∿ equivalent at function type if for all pr : Δ ≥ Γ.  (t  ⟨ π pr ⟩ ⋆ u) ↯ (T pr U) ,  for u, U. u ↯ U
[_,_]_∿_ : ∀ Γ A (M : Γ ⊢ A) (u : Γ ⊩ A) → Set
[ Γ , ♭ ] M ∿ u = ∀ {Δ} (c : Δ ≥ _) → Δ ⊢ ♭ ∋ M ⟨ π c ⟩ ≅ u c
[ Γ , A ⇒ B ] M ∿ u =
  ∀ {Δ} (c : Δ ≥ Γ) {N v} (cv : [ Δ , A ] N ∿ v) → [ Δ , B ] M ⟨ π c ⟩ ⋆ N ∿ u c v


-- ↯ε relates term substitutions to value environments.
-- current definition seems a bit messy. Is there a reason? Why not use V2?
data [_,_]ε_∿_ Δ : ∀ Γ (γ : Δ ⇛ Γ) (ρ : Δ ⊩ᵉ Γ) → Set where
  ε : ∀ {γ : Δ ⇛ ε} → [ Δ , ε ]ε γ ∿ tt
  ∙ : ∀ {Γ x A f} {γ : Δ ⇛ Γ ∙[ x ∶ A ]⊣ f} {ρ : Δ ⊩ᵉ Γ} (πγρ : [ Δ ,  Γ ]ε π lemma₅ ⊙ γ ∿ ρ)
      {u : Δ ⊩ A} (xu : [ Δ , A ] [ _ ∋ x ↳ here! ] ⟨ γ ⟩ ∿ u) →
      [ Δ , Γ ∙[ x ∶ A ]⊣ f ]ε γ ∿ (ρ , u)

-- why not the following? todo test if all works this way. (V2)
--  ∙ : ∀ {Γ x A f} {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (γ∿ρ : [ Δ , Γ ]ε γ ∿ ρ)
--      (T : Δ ⊩ A) (t : Δ ⊢ A) (xu : [ Δ , A ]  t ∿ T) →
--      [ Δ , Γ ∙[ x ∶ A ]⊣ f ]ε (γ [ x ↦ t ]) ∿ (ρ , T)

-- βη-equivalent terms are ↯-related  to the same semantic values.  
-- (so if I can show that 
--       1. t is ↯-related  to ⟦t⟧  and 
--       2. two semantic values related to a single term are equal in model Eq...
--   then we should get proper soundness proof)
∿≡-cast : ∀ {Γ} A {M M' u} (eq : Γ ⊢ A ∋ M ≅ M') (cv : [ Γ , A ] M ∿ u) → [ Γ , A ] M' ∿ u
∿≡-cast ♭ {M} {M'} {u} eq cv = λ {Δ} c → ≡*-trans (≡*-cong cs₁ (≡*-sym eq)) (cv c)
∿≡-cast (A ⇒ B) {M} {M'} {u} eq cv = λ {Δ} c {N} {v} cvNv → ∿≡-cast B (≡*-cong (ca₁ ∘ cs₁) eq) (cv c cvNv)



-- βη-equivalent subsitutions are ↯ε-related to the same semantic environments.
∿≡ε-cast : ∀ {Δ} Γ {γ₁ γ₂ ρ} (eq : Δ ⊢ Γ ∋ γ₁ ≅ˢ γ₂) (cv : [ Δ , Γ ]ε γ₁ ∿ ρ) → [ Δ , Γ ]ε γ₂ ∿ ρ
∿≡ε-cast .ε eq ε = ε
∿≡ε-cast (Γ ∙[ x ∶ A ]⊣ f) eq (∙ cv xu) =
   ∙ (∿≡ε-cast Γ (≡*-cong c∘₂ eq) cv) (∿≡-cast A (≡*-cong cs₂ eq) xu)



-- ∿ relation lifts via context ordering (here lifting through c : Δ ≥ Γ)
∿↑ : ∀ {Γ Δ} A {M u} (c : Δ ≥ Γ) (cv : [ Γ , A ] M ∿ u) → [ Δ , A ] M ⟨ π c ⟩ ∿ ↑[ c , A ]⟨ u ⟩
∿↑ ♭ pr cv = λ {Ε} inc →
 ≡*-trans (lstep :s⊙ (lstep (cs₂ ∶⊙∶π) refl)) (cv _)
∿↑ (A ⇒ B) pr cv = λ {Δ} inc {u} {U} cvU →
  ∿≡-cast B (≡*-sym (lstep (ca₁ :s⊙) (lstep (ca₁ (cs₂ ∶⊙∶π)) refl))) (cv _ cvU)


-- (occ at explicit-subst) ∿-relates to (lookup at occ in semantic env) if explicit-subst and semantic env ∿ε related.
∿-lookup : ∀ {Δ} Γ {x A} occ {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (cv : [ Δ , Γ ]ε γ ∿ ρ) →
            [ Δ , A ] [ Γ ∋ x ↳ occ ] ⟨ γ ⟩ ∿ lookup Γ ρ occ
∿-lookup .ε () ε
∿-lookup (Γ ∙[ x ∶ A ]⊣ f) here! (∙ cv xu) = xu
∿-lookup (Γ ∙[ x ∶ A ]⊣ f) {y} {B} (there .f pr) (∙ cv xu) =
  ∿≡-cast B (rstep :s⊙ (lstep (cs₁ :v₂) refl)) (∿-lookup Γ pr cv)



-- explicit-subst composition and semantic lifting preserve ↯ε-relation
∿π : ∀ {Δ} Γ {Ε} (c : Ε ≥ Δ) {γ : Δ ⇛ Γ} {ρ} (cv : [ Δ , Γ ]ε γ ∿ ρ) →
      [ Ε , Γ ]ε γ ⊙ π c ∿ ↑ᵉ[ c , Γ ]⟨ ρ ⟩
∿π .ε c ε = ε
∿π (Γ ∙[ x ∶ A ]⊣ f) c (∙ cv xu) =
  ∙ (∿≡ε-cast Γ (lstep ⊙-assoc refl) (∿π Γ c cv)) (∿≡-cast A (lstep :s⊙ refl) (∿↑ A c xu))

-- composing with projection  and  projecting semantic values preserve  ∿ε -relation
∿πᵉ : ∀ {Δ} Γ {Ε} (c : Γ ≥ Ε) {γ : Δ ⇛ Γ} {ρ} (cv : [ Δ , Γ ]ε γ ∿ ρ ) → [ Δ , Ε ]ε π c ⊙ γ ∿ πᵉ c ρ
∿πᵉ Γ stop cv = ε
∿πᵉ .ε (step c () f) ε
∿πᵉ (Γ ∙[ x ∶ A ]⊣ f) (step {Δ} {y} {B} c occ f') cv =
  ∙ (∿≡ε-cast Δ (≡*-sym (rstep ⊙-assoc (lstep (c∘₁ ∶⊙∶π) refl)))
    (∿πᵉ (Γ ∙[ x ∶ A ]⊣ f) c cv))
    (∿≡-cast B (≡*-sym (rstep :s⊙ (lstep (cs₁ :v₂) refl))) (∿-lookup _ occ cv))


mutual

  -- if p, P related by ∿ε  then t ⟨ ρ ⟩ ∿ ⟦ t ⟧t P
  lemma₈ : ∀ {A Γ Δ} M {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (cv : [ Δ , Γ ]ε γ ∿ ρ) → [ Δ , A ] M ⟨ γ ⟩ ∿ ⟦ M ⟧t ρ
  lemma₈ [ Γ ∋ x ↳ occ ] cv = ∿-lookup Γ occ cv
  lemma₈ {A ⇒ B} (∶λ x # f ⇨ t) cv =
   λ {Ε} c {N} {v} cvNv → ∿≡-cast B (≡*-sym (lstep (ca₁ :s⊙) (lstep :β refl))) (lemma₈ t
   (∙ (∿≡ε-cast _ (≡*-sym (lstep ∶π∶ext refl)) (∿π _ c cv)) (∿≡-cast A (rstep :v₁ refl) cvNv)))
  lemma₈ {A} (M ⋆ N) cv =
    ∿≡-cast A (lstep (ca₁ :sid) (rstep :sapp refl)) (lemma₈ M cv lemma₃ (lemma₈ N cv))
  lemma₈ {A} (M ⟨ γ ⟩) cv = ∿≡-cast A (rstep :s⊙ refl) (lemma₈ M (∿subst _ γ cv))

  -- lemma₈ but for substitutions, not terms
  -- i.e. if p, P related by ∿ε  then  (γ ⊙ ρ)  ∿ε  (⟦ γ ⟧s P)
  ∿subst : ∀ Γ {Δ} (γ : Δ ⇛ Γ) {Ε} {δ : Ε ⇛ Δ} {ρ : Ε ⊩ᵉ Δ} (cv : [ Ε , Δ ]ε δ ∿ ρ) → [ Ε , Γ ]ε γ ⊙ δ ∿ ⟦ γ ⟧s ρ
  ∿subst Γ (π c) cv = ∿πᵉ _ c cv
  ∿subst Γ (γ ⊙ δ) cv = ∿≡ε-cast Γ (rstep ⊙-assoc refl) (∿subst Γ γ (∿subst _ δ cv))
  ∿subst (Γ ∙[ x ∶ A ]⊣ f) (γ [ .x ↦ M ]) cv = 
   ∙ (∿≡ε-cast Γ (≡*-sym (rstep ⊙-assoc (lstep (c∘₁ ∶π∶ext) refl))) (∿subst Γ γ cv))
      (∿≡-cast A (≡*-sym (lstep (cs₂ ∶ext∶⊙) (lstep :v₁ refl))) (lemma₈ M cv))


mutual 

  lemma₉ : ∀ {A Γ} M u (cv : [ Γ , A ] M ∿ u) → (Γ ⊢ A ∋ M ≅ reify Γ A u)
  lemma₉ M u cv = {!!}

  ∿-val : ∀ {A Γ} M (f : Γ ⊢⇑ A)(h : ∀ {Δ} (c : Δ ≥ Γ) → Δ ⊢ A ∋ M ⟨ π c ⟩ ≅ f c) → [ Γ , A ] M ∿ val Γ A f
  ∿-val M f Mf≅ = {!!}


π∿id↑ᵉ : ∀ {Γ Δ} (c : Δ ≥ Γ) → [ Δ , Γ ]ε π c ∿ id↑ᵉ c
π∿id↑ᵉ c = {!!}

theorem₂ : ∀ {Γ A} (M : Γ ⊢ A) → Γ ⊢ A ∋ M ≅ nf M
theorem₂ M = {!!}


-- now easy to prove Theorem 3. 
-- proof: know by corollary 1 that nf(M) = nf(N)

theorem₃ : ∀ {Γ A} M N (eq : Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idε Γ) , ⟦ N ⟧t (idε Γ) ]) → Γ ⊢ A ∋ M ≅ N
theorem₃ M N eq = {!!}



----- Completeness of substitution conversions. 
reifyˢ : ∀ Δ Γ (ρ : Δ ⊩ᵉ Γ) → (Δ ⇛ Γ)
reifyˢ Δ ε tt = π stop
reifyˢ Δ (Γ ∙[ x ∶ A ]⊣ f) (ρ , v) = (reifyˢ  Δ Γ ρ)[ x ↦ reify Δ A v ]

nfˢ : ∀ {Γ Δ} (M : Δ ⇛ Γ) → Δ ⇛ Γ
nfˢ {Γ} {Δ} γ = reifyˢ Δ Γ (⟦ γ ⟧s (idε Δ))

-- completeness result follows from similar work as for proof trees. 
-- i.e. prove γ ≅ˢ nf γ   


-- Theorem5 ∈ (nf(M)≡nf(N)) → M ≅ N   (Decision algorithm is correct)
-- by Theorem2 we have M ≅ nf(M) and N ≅ nf(N) and, by hypothesis, nf(M)≡nf(N) and ≅-refl,
-- we get by transitivity of ≅, that M ≅ N.
theorem₅ : ∀ {Γ A}(M N : Γ ⊢ A)(idnf : nf M ≡ nf N) → Γ ⊢ A ∋ M ≅ N
theorem₅ M N idnf = {!!}

-- Theorem6 ∈ (M ≅ N) → nf(M) ≡ nf(N)    (Decision algorithm is complete)
-- since by Theorem4 and the hypothesis, M≅N we get Eq([M]id,[N]id) and by corollary1 
-- we get nf M ≡ nf N.
theorem₆ : ∀ {Γ A} (M N : Γ ⊢ A)(cv : Γ ⊢ A ∋ M ≅ N) → nf M ≡ nf N
theorem₆ M N cv = {!!}

--- Normal forms

mutual 
  data enf : ∀ {Γ A}(M : Γ ⊢ A) → Set where
    enf1 : ∀ {Γ x A B f}(M : Γ ∙[ x ∶ A ]⊣ f ⊢ B)(Me : enf M) → enf (∶λ x # f ⇨ M)
    enf2 : ∀ {Γ}(M : Γ ⊢ ♭)(Ma : anf M) → enf M

  data anf : ∀ {Γ A}(M : Γ ⊢ A) → Set where
    anf1 : ∀ {Γ x A}{occ : [ x ∶ A ]∈ Γ} → anf [ Γ ∋ x ↳ occ ]
    anf2 : ∀ {Γ A B} (M : Γ ⊢ A ⇒ B) (N : Γ ⊢ A)(Ma : anf M)(Ne : enf N) → anf (M ⋆ N)


-- Goal: prove enf(nf M)  
--  define kripke logical predicate KN , such that KN⟦M⟧ and if KN(u), then enf(reify u).
--  as before we define by induction on the type.
NV : ∀ {Γ A} (v : Γ ⊩ A) → Set
NV {Γ} {♭} v = ∀ {Δ} (c : Δ ≥ Γ) → anf (v c)
NV {Γ} {A ⇒ B} v = ∀ {Δ : Context} (c : Δ ≥ Γ) (u : Δ ⊩ A) (nu : NV {Δ} {A} u) → NV {Δ} {B} (v c u)


-- similar property of substitutions.
-- option 1
NVε : ∀ {Δ} {Γ} (ρ : Δ ⊩ᵉ Γ) → Set
NVε {Δ} {ε} tt = ⊤
NVε {Δ} {Γ ∙[ x ∶ A ]⊣ f} (ρ , v) = NVε {Δ} {Γ} ρ × NV {Δ} {A} v

-- option 2 (data)
-- data NVε : ∀ {Δ Γ} (ρ : Δ ⊩ᵉ Γ) → Set where
--   εN : ∀ {Δ} → NVε {Δ} {ε} tt
--   ∙N : ∀ {Δ Γ x A f} {ρ : Δ ⊩ᵉ Γ} (nρ : NVε {Δ} {Γ} ρ) {v : Δ ⊩ A} (nv : NV {Δ} {A} v) → NVε {Δ} {Γ ∙[ x ∶ A ]⊣ f} (ρ , v)


-- lemmas from 77

-- (v : Δ⊩A) N(v) (c : Γ≥Δ) → N(↑c(v))

-- (ρ : 􏰰Γ ⊩ᵉ Δ) N(ρ) (occ : [ x ∶ A ]∈ Δ) → N(lookup(ρ, Δ ∋ x ↳ occ)) 

-- (ρ : Γ₀ ⊩ᵉ Δ) N(ρ) (c : Γ₁ ≥ Γ₀) → N(↑c(ρ)) 

-- (ρ : Γ ⊩ᵉ Δ₁) N(ρ) (c : Δ₁ ≥ Δ₀) N(↓c(ρ))

-- Lemma 10 (M : Γ ⊢ A) (ρ : Δ ⊩ᵉ Γ) N(ρ) → N(⟦M⟧ρ)
-- (proved mutually with   (γ : Δ ⇛ Γ)(ρ : Θ ⊩ᵉ Δ) N(ρ) → N(⟦γ⟧ρ)


-- Lemma 11 : (v : Γ ⊩ A) (vn : N v) → enf (reify (v))
--   is shown mutually with
--   Lemma11-sub : (f ∈ Γ ⊢⇑ A)(h : ∀ {Δ} (c : Δ ≥ Γ) → anf (f c)) → N (val Γ A f)
-- proof by induction on type

-- Now easy to show N id   

-- Theorem 7: (M : Γ ⊢ A) → enf(nf M)
-- by simple application of lemma 10 and lemma 11

-- Todo-Exercise: paper says we can use these results to show that 
-- (λ x:A.M) ≅ (λ y:A.N) ⇒ M ⟨x ↦ z⟩ ≅ N⟨y ↦ z⟩ for z fresh 
-- i.e.
-- Γ ⊢ A ⇒ B ∋ (∶λ x # f . M) ≅ (∶λ y # f . N)
--         → M ⟨ π (lemma₃ Γ) [ x ↦ z ] ⟩ ≅ N ⟨ π (lemma₃ Γ) [ y ↦ z ] ⟩ 



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
