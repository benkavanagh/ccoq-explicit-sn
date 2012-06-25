module Kripke where

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
open import PT

-- first define Kripke models
record Kripke : Set₁ where
   constructor kripke
   field 
     W : Set 
     _≥ʷ_ : Rel W Lvl.zero   -- preorder rel
     isPO : IsPreorder (_≡_ {Lvl.zero} {W})  _≥ʷ_
     uniq≥ : {w₁ w₂ : W}(c₁ c₂ : w₁ ≥ʷ w₂) → c₁ ≡ c₂
     G : W → Set     -- Gw w₁ = interpretation of ⊙ at w₁


--  naturally one might try to use a datatype.
--  data  _⊩_  : (w : W) (A : Type) → Set where
--   Ground : ∀{w : W} → (f : (w' : W ) (c : w' ≥ʷ w) → (G w')) → w ⊩ ♭ 
--   Lambda : ∀{w : W}{A}{B} (f : (w' : W) (c : w' ≥ʷ w) (fc : w' ⊩ A) → (w' ⊩ B))  → w ⊩ (A ⇒ B)
--
--  This doesn't work because of positivity requirements on the datatype. 
--  Instead, as we did with NBE in agda course we define the model by recursion on the type rather than
--  as an inductive type. Using this method there is no positivity problem.


module KSem  (K : Kripke )  where 
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
    Eq⟨ w ⊩ ♭ ⟩[ u , v ] = (∀ {w'} (c : w' ≥ʷ w) → u c ≡ v c)
    Eq⟨ w ⊩ A ⇒ B ⟩[ u₁ , u₂ ] =
      ∀ {w'} (c : w' ≥ʷ w) {v : w' ⊩ A} (uni : Uni⟨ w' ⊩ A ⟩ v) → Eq⟨ w' ⊩ B ⟩[ u₁ c v , u₂ c v ]

    -- Uni: all ground semantic objects are uniform
    -- a semantic object of functional type is uniform 
    --   (1) maps uniform input objects to uniform output objects.
    --   (2) maps equal, uniform objects to equal output objects.
    --   (3) application and monotonicity commute. 
    Uni⟨_⊩_⟩_ : ∀ w A (u : w ⊩ A) → Set 
    Uni⟨ w ⊩ ♭ ⟩ u =  ⊤
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

  Eq-sym : ∀ A {w u v} (eq : Eq⟨ w ⊩ A ⟩[ u , v ]) → Eq⟨ w ⊩ A ⟩[ v , u ]
  Eq-sym ♭ eq = sym ∘ eq 
  Eq-sym (A ⇒ B) eq = λ c u → Eq-sym B ((eq c u))

  Eq-trans : ∀ A {w u₁ u₂ u₃} (eq₁ : Eq⟨ w ⊩ A ⟩[ u₁ , u₂ ]) (eq₂ : Eq⟨ w ⊩ A ⟩[ u₂ , u₃ ]) →
             Eq⟨ w ⊩ A ⟩[ u₁ , u₃ ]
  Eq-trans ♭ eq₁ eq₂ = λ c → trans (eq₁ c) (eq₂ c) 
  Eq-trans (S ⇒ T) eq₁ eq₂ = λ c u' → Eq-trans T (eq₁ c u') (eq₂ c u')


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
  Eq-cong-↑ : ∀ A {w w'} (c : w' ≥ʷ w) {u₁ u₂} (eq : Eq⟨ w ⊩ A ⟩[ u₁ , u₂ ]) →
             Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]⟨ u₁ ⟩ , ↑[ c , A ]⟨ u₂ ⟩ ]
  Eq-cong-↑ ♭ c eq = λ c' → eq _
  Eq-cong-↑ (A ⇒ B) c eq = λ c' {v} uv → eq _ uv

   -- "↑ gives uniform output for uniform input"
  Uni↑ : ∀ A {w w' : W} (c : w' ≥ʷ w) u (uni : Uni⟨ w ⊩ A ⟩ u) → Uni⟨ w' ⊩ A ⟩ (↑[ c , A ]⟨ u ⟩)
  Uni↑ ♭ {w}{w'} c u uni = tt
  Uni↑ (A ⇒ B) {w} {w'} c u uni = 
            ( (λ c' univ → ((Σ.proj₁ uni) (P.trans c' c) univ)) ,
             ( (λ c' uni₂ uni₂' eq → (Σ.proj₁ (Σ.proj₂ uni)) (P.trans c' c) uni₂ uni₂' eq) ,
              (λ c₁ c₂ c₃ uni₂ → (Σ.proj₂ (Σ.proj₂ uni)) (P.trans c₁ c) c₂ (P.trans c₃ c) uni₂) )) 

  -- subst(simplified).  (P : A → Set)  →  P  Respects ≡
  --             i.e.           (P : A → Set)  →  x ≡ y → P x →  P y

  -- Eq↑: lifting by identity has no effect
  Eq↑-id : ∀ A {w} u (c : w ≥ʷ w) → Eq⟨ w ⊩ A ⟩[ ↑[ c , A ]⟨ u ⟩ , u ]
  Eq↑-id  ♭ u c = λ c' → cong u (uniq≥ _ _)
  Eq↑-id  (A ⇒ B) {w} u c = 
        λ {w'} c' {v} uni-v → subst ((λ c → Eq⟨ w' ⊩ B ⟩[ u c v , u c' v ])) (uniq≥ _ _) (Eq-refl B _)

  
  -- Eq↑↑ :  repeated lifting equal to lifting by transitive order.    (again uniq≥)
  Eq↑↑ : ∀ A {w} u {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) →
         Eq⟨ w₂ ⊩ A ⟩[ ↑[ c₂ , A ]⟨ ↑[ c₁ , A ]⟨ u ⟩ ⟩ , ↑[ c₃ , A ]⟨ u ⟩ ]
  Eq↑↑ ♭ u c₁ c₂ c₃ = λ c → cong u (uniq≥ _ _)
  Eq↑↑ (A ⇒ B) {w} u {w₁} {w₂} c₁ c₂ c₃ = 
        λ {w' } c {v } uni-v → subst (λ c' → Eq⟨ w' ⊩ B ⟩[ u c' v , u (P.trans c c₃) v ]) (uniq≥ _ _) (Eq-refl B (u _ v))

  -- Eq-coherence-app↑  semantic application of u to value v at higher world w' is equal to  
  -- application of u lifted to w' to v (via refl)
  --                
  Eq-coherence-app↑ : ∀ {w A B} (u : w ⊩ A ⇒ B) {w'} (c : w' ≥ʷ w) {v} →
           Eq⟨ w' ⊩ B ⟩[ u c v , (↑[ c , A ⇒ B ]⟨ u ⟩) P.refl v ]
  Eq-coherence-app↑ {w} {A} {B} u {w'} c {v} rewrite (uniq≥ (P.trans P.refl c) c) = Eq-refl B _ 


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
  Eq-lookup : ∀ {Δ Γ w ρ} (c : Δ ≥ Γ) {x A} (occ₁ : [ x ∶ A ]∈ Δ) (occ₂ : [ x ∶ A ]∈ Γ) →
              Eq⟨ w ⊩ A ⟩[ lookup Δ ρ occ₁ , lookup Γ (πᵉ c ρ) occ₂ ]
  Eq-lookup stop occ ()
  Eq-lookup {Δ} {Γ ∙[ x ∶ A ]⊣ f} {w} {ρ} (step c occ₁ .f) {.x} {.A} occ₂ here! = lookup-uniq ρ occ₂ occ₁
  Eq-lookup (step c occ f) pr (there .f pr') = Eq-lookup c pr pr' 


  -- lifting/weakening and lookup are commuting / coherent operations
  Eq↑-lookup : ∀ {Γ w w'} (c : w' ≥ʷ w) ρ {x A} (occ : [ x ∶ A ]∈ Γ) →
               Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]⟨ lookup Γ ρ occ ⟩ , lookup Γ ↑ᵉ[ c , Γ ]⟨ ρ ⟩ occ ]
  Eq↑-lookup {ε} c ρ ()
  Eq↑-lookup {Γ ∙[ x ∶ A ]⊣ f} c (_ , r) here! = Eq-refl A ↑[ c , A ]⟨ r ⟩
  Eq↑-lookup c (ρ , _) (there f pr) = Eq↑-lookup c ρ pr
 
  Eq-cong-lookup : ∀ {Γ A w} {ρ₁ ρ₂ : w ⊩ᵉ Γ} (eq : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ]) {x} (occ : [ x ∶ A ]∈ Γ)
                       → Eq⟨ w ⊩ A ⟩[ lookup Γ ρ₁ occ , lookup Γ ρ₂ occ ]
  Eq-cong-lookup {ε} eq ()
  Eq-cong-lookup {Γ ∙[ x ∶ A ]⊣ f} (eqρ , eqv) here! = eqv
  Eq-cong-lookup {Γ ∙[ x ∶ A ]⊣ f} (eqρ , eqv) (there .f occ) = Eq-cong-lookup eqρ occ 

  -- projection from Γ semantic env to Δ semantic env gives same result
  -- as projection from Γ extended with fresh variable x, since obviously x cannot 
  -- be in Δ (hence refuteFresh case)
  Eqπ-step : ∀ {w Γ ρ Δ} (c₁ : Γ ≥ Δ) {x A v f} (c₂ : Γ ∙[ x ∶ A ]⊣ f ≥ Δ) →
             Eq⟨ w ⊩ᵉ Δ ⟩[ πᵉ c₂ (ρ , v) , πᵉ c₁ ρ ]
  Eqπ-step stop c₂ = tt
  Eqπ-step (step c₁ occ f) (step c₂ (here! {_} {g}) .f) = ⊥-elim (refuteFresh g occ)
  Eqπ-step (step c₁ occ f) (step c₂ (there f₁ occ₁) .f) =
    Eqπ-step c₁ c₂ , Eq-lookup (step c₁ occ f) occ₁ here!

  π-step≡ : ∀ {w Γ Δ} {ρ : w ⊩ᵉ Γ} (c₁ : Γ ≥ Δ) {x A v f} (c₂ : Γ ∙[ x ∶ A ]⊣ f ≥ Δ) →
              πᵉ c₂ (ρ , v) ≡ πᵉ c₁ ρ 
  π-step≡ {w} {Γ} {ε} stop stop = refl 
  π-step≡ (step c₁ occ f) (step c₂ (here! {_} {g}) .f) = ⊥-elim (refuteFresh g occ) 
  π-step≡ (step c₁ occ₁ g) {x} {A} {v} (step c₂ (there f₁ occ₂) .g) =  cong₂ (λ p v → (p , v)) (π-step≡ c₁ c₂) (cong _ (lemma₆ occ₂ occ₁)) 

  -- Sem env ρ is Eq to identity (c : Γ ≥ Γ) restriction on ρ.
  Eqπ-id : ∀ Γ {w ρ} (c : Γ ≥ Γ) → Eq⟨ w ⊩ᵉ Γ ⟩[ πᵉ c ρ , ρ ]
  Eqπ-id ε stop = tt
  Eqπ-id (Γ ∙[ x ∶ A ]⊣ f) (step c here! .f) =
    Eqᵉ-trans Γ (Eqπ-step lemma₃ c) (Eqπ-id Γ _) , Eq-refl A _
  Eqπ-id (Γ ∙[ x ∶ A ]⊣ f) (step c (there .f occ) .f) = ⊥-elim (refuteFresh f occ)

  π-id≡ : ∀ Γ {w} (c : Γ ≥ Γ) (ρ : w ⊩ᵉ Γ)  →  πᵉ c ρ ≡ ρ 
  π-id≡ ε  stop tt = refl
  π-id≡ (Γ ∙[ x ∶ A ]⊣ f) (step c here! .f) (ρ , v)  = cong (λ ρ → (ρ , v)) (trans (π-step≡ lemma₃ c) (π-id≡ Γ lemma₃ ρ )) 
  π-id≡  (Γ ∙[ x ∶ A ]⊣ f) (step c (there .f occ) .f) (ρ , v)  =  ⊥-elim (refuteFresh f occ) 


  -- Sem env ρ is equal to ρ lifted by identity on world c : w ≥ʷ w
  Eqᵉ↑-id : ∀ Γ {w ρ} (c : w ≥ʷ w) → Eq⟨ w ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ρ ⟩ , ρ ]
  Eqᵉ↑-id ε c = tt
  Eqᵉ↑-id (Γ ∙[ x ∶ A ]⊣ f) c = Eqᵉ↑-id Γ c , Eq↑-id A _ c

  -- multiple projections equal to projection by composed ordering (by trans)
  Eqππ : ∀ Γ Δ Ε {w} {ρ : w ⊩ᵉ Ε} (c₁ : Δ ≥ Γ) (c₂ : Ε ≥ Δ) (c₃ : Ε ≥ Γ) →
         Eq⟨ w ⊩ᵉ Γ ⟩[ πᵉ c₁ (πᵉ c₂ ρ) , πᵉ c₃ ρ ]
  Eqππ .ε Δ Ε stop c₂ c₃ = tt
  Eqππ (Γ ∙[ x ∶ A ]⊣ f) Δ Ε (step c₁ occ .f) c₂ c₃
    rewrite lemma₇ c₃ (lemma₄ c₂ (step c₁ occ f)) =
    Eqππ Γ Δ Ε c₁ c₂ _ , Eq-sym A (Eq-lookup c₂ (lemma₂ c₂ occ) occ)

  -- multiple liftings equivalent to lifting by composed ordering (by trans)
  Eqᵉ↑↑ : ∀ Γ {w w₁ w₂} {ρ : w ⊩ᵉ Γ} (c₂ : w₂ ≥ʷ w₁) (c₁ : w₁ ≥ʷ w) (c₃ : w₂ ≥ʷ w) →
          Eq⟨ w₂ ⊩ᵉ Γ ⟩[ ↑ᵉ[ c₂ , Γ ]⟨ ↑ᵉ[ c₁ , Γ ]⟨ ρ ⟩ ⟩ , ↑ᵉ[ c₃ , Γ ]⟨ ρ ⟩ ]
  Eqᵉ↑↑ ε c₁ c₂ c₃ = tt
  Eqᵉ↑↑ (Γ ∙[ x ∶ A ]⊣ f) c₁ c₂ c₃ = (Eqᵉ↑↑ Γ c₁ c₂ c₃) , (Eq↑↑ A _ c₂ c₁ c₃)

  -- Equality preserved by lifting and projection
  Eqᵉ↑π : ∀ {Γ} Δ {w} w' {ρ : w ⊩ᵉ Γ} (c : w' ≥ʷ w) (c' : Γ ≥ Δ) →
          Eq⟨ w' ⊩ᵉ Δ ⟩[ ↑ᵉ[ c , Δ ]⟨ πᵉ c' ρ ⟩ , πᵉ c' ↑ᵉ[ c , Γ ]⟨ ρ ⟩ ]
  Eqᵉ↑π .ε w' c stop = tt
  Eqᵉ↑π (Δ ∙[ x ∶ A ]⊣ f) w' {ρ} c (step c' occ .f) = Eqᵉ↑π Δ w' c c' , Eq↑-lookup c ρ occ

  -- Equality preserved by lifting only
  -- probably more work work to show via Eqᵉ↑π , π-id≡ , etc. rather than simply defining directly. 
  Eqᵉ↑-refl : ∀ {Γ} {w} w' {ρ : w ⊩ᵉ Γ} (c : w' ≥ʷ w)  →  Eq⟨ w' ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ρ ⟩ , ↑ᵉ[ c , Γ ]⟨ ρ ⟩ ]
  Eqᵉ↑-refl {Γ} {w} w' {ρ} c = subst₂ (λ ρ' ρ'' →  Eq⟨ w' ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ρ' ⟩ , ρ'' ])
                                                   (π-id≡ Γ lemma₃ ρ) 
                                                   (π-id≡ Γ lemma₃ (↑ᵉ[ c , Γ ]⟨ ρ ⟩))
                                                   pr 
      where 
      pr :    Eq⟨ w' ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ πᵉ (lemma₃ {Γ}) ρ ⟩ , πᵉ (lemma₃ {Γ}) ↑ᵉ[ c , Γ ]⟨ ρ ⟩ ]
      pr =  Eqᵉ↑π {Γ} Γ {w} w' {ρ} c lemma₃ 

  -- ↑ is a congurence for Eqᵉ.  I could get Eqᵉ↑-refl by composing Eqᵉ↑ ,  Eqᵉ-refl
  Eqᵉ-cong-↑ : ∀ {Γ} {w} w' (c : w' ≥ʷ w)  {ρ₁ ρ₂ : w ⊩ᵉ Γ} (eq : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ]) →  Eq⟨ w' ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ρ₁ ⟩ , ↑ᵉ[ c , Γ ]⟨ ρ₂ ⟩ ]
  Eqᵉ-cong-↑ {ε} w' c eq = tt
  Eqᵉ-cong-↑ {Γ ∙[ x ∶ A ]⊣ f} w' c (eqρ , eqv) = (Eqᵉ-cong-↑ {Γ} w' c eqρ , Eq-cong-↑ A c eqv ) 

  -- πᵉ is a congruence for Eq.
  Eqᵉ-cong-πᵉ : ∀ {Γ Δ} {w} (c : Γ ≥ Δ)  {ρ₁ ρ₂ : w ⊩ᵉ Γ} (eq : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ]) →  Eq⟨ w ⊩ᵉ Δ ⟩[ πᵉ c ρ₁ , πᵉ c ρ₂ ]
  Eqᵉ-cong-πᵉ stop eq = tt
  Eqᵉ-cong-πᵉ (step c here! f') (eqρ , eqv) = (Eqᵉ-cong-πᵉ c (eqρ , eqv) , eqv)
  Eqᵉ-cong-πᵉ (step c (there f occ) f') (eqρ , eqv) = ( Eqᵉ-cong-πᵉ c (eqρ , eqv) , Eq-cong-lookup eqρ occ ) 


  Uni-lookup : ∀ { w Γ A x} (ρ : w ⊩ᵉ Γ) (up : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) (occ : [ x ∶ A ]∈ Γ) → Uni⟨ w ⊩ A ⟩ (lookup Γ ρ occ)
  Uni-lookup {w} {ε} _ _ ()
  Uni-lookup {w} {Γ' ∙[ x' ∶ A ]⊣ f} (ρ' , v) (uρ , uv) here! = uv
  Uni-lookup {w} {Γ' ∙[ x' ∶ A ]⊣ f} (ρ' , v) (uρ , uv) (there .f occ) = Uni-lookup ρ' uρ occ

  Uniᵉ↑ : ∀ Γ {w w' ρ } (c : w' ≥ʷ w) (uρ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) → Uni⟨ w' ⊩ᵉ Γ ⟩ ↑ᵉ[ c , Γ ]⟨ ρ ⟩
  Uniᵉ↑ ε c uρ = tt
  Uniᵉ↑ (Γ ∙[ x ∶ A ]⊣ f) {w} {w'} {(ρ , v)} c (uρ , uv) = (Uniᵉ↑ Γ c uρ , Uni↑ A c v uv)

  Uniᵉπ : ∀ {Γ Δ w ρ } (c : Γ ≥ Δ) (uρ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) → Uni⟨ w ⊩ᵉ Δ ⟩ πᵉ c ρ 
  Uniᵉπ stop uρ = tt
  Uniᵉπ (step c here! f') (uρ , uv) = (Uniᵉπ c (uρ , uv) , uv)
  Uniᵉπ (step c (there f' occ) f) (uρ , uv) = ( Uniᵉπ c (uρ , uv) , Uni-lookup _ uρ occ) 


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
  mutual 
    Uni-⟦⟧t : ∀ {Γ w A} (M : Γ ⊢ A) ρ (uni : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) → Uni⟨ w ⊩ A ⟩ (⟦ M ⟧t ρ)
    -- Γ ∋ x ↳ occ
    Uni-⟦⟧t {Γ} [ .Γ ∋ x ↳ occ ] ρ uni = Uni-lookup ρ uni occ
    -- ∶λ x # f ⇨ M
    Uni-⟦⟧t {Γ} {w} {A ⇒ B} (∶λ x # f ⇨ M) ρ uni  = 
                 ((λ c uv → Uni-⟦⟧t M _ ( Uniᵉ↑ Γ c uni , uv )) , 
                     ( (λ{w'} c {v₁} {v₂} uv₁ uv₂ eqv → 
                            Eq-⟦⟧t-compat {w'} {Γ ∙[ x ∶ A ]⊣ f} {B}  M
                                                  { (↑ᵉ[ c , Γ ]⟨ ρ ⟩ , v₁)}  {(↑ᵉ[ c , Γ ]⟨ ρ ⟩ , v₂)} 
                                                  ( Uniᵉ↑ Γ c uni  , uv₁ ) ( Uniᵉ↑ Γ c uni  , uv₂ ) 
                                                  ((Eqᵉ↑-refl {Γ} w' c , eqv))) , 
                         (λ {w₁}{w₂}c₁ c₂ c₃ {v} uv → Eq-trans B 
                                                               (Eq-⟦⟧t↑-coherence M 
                                                                                 (↑ᵉ[ c₁ , Γ ]⟨ ρ ⟩ , v) 
                                                                                 (Uniᵉ↑ Γ c₁ uni , uv) c₂)
                                                               ((Eq-⟦⟧t-compat {w₂}  {Γ ∙[ x ∶ A ]⊣ f}  {B} M
                                                                                        {(↑ᵉ[ c₂ , Γ ]⟨ ↑ᵉ[ c₁ , Γ ]⟨ ρ ⟩ ⟩ , ↑[ c₂ , A ]⟨ v ⟩)}
                                                                                        {(↑ᵉ[ c₃ , Γ ]⟨ ρ ⟩ , ↑[ c₂ , A ]⟨ v ⟩)}
                                                                                         (Uniᵉ↑ Γ c₂ (Uniᵉ↑ Γ c₁ uni) , Uni↑ A c₂ v uv )
                                                                                         ((Uniᵉ↑ Γ c₃ uni , Uni↑ A c₂ v uv )) 
                                                                                         ((Eqᵉ↑↑ Γ c₂ c₁ c₃ , Eq-refl A _)))))))
    -- M ⋆ N
    Uni-⟦⟧t {Γ}{w}{B} (_⋆_ {.Γ} {A} {.B} M N) ρ uni with (Uni-⟦⟧t {Γ}{w}{A ⇒ B} M ρ uni) | (Uni-⟦⟧t N ρ uni) 
    Uni-⟦⟧t {Γ}{w}{B} (M ⋆ N) ρ uni | ihM | ihN = (Σ.proj₁ ihM) P.refl ihN 
    -- M ⟨ γ ⟩
    Uni-⟦⟧t (M ⟨ γ ⟩) ρ uni = Uni-⟦⟧t M (⟦ γ ⟧s ρ) (Uni-⟦⟧s γ ρ uni) 


    Uni-⟦⟧s : ∀{Γ Δ w} (γ : Δ ⇛ Γ) ρ (uni : Uni⟨ w ⊩ᵉ Δ ⟩ ρ) → Uni⟨ w ⊩ᵉ Γ ⟩ (⟦ γ ⟧s ρ)
    Uni-⟦⟧s (π c) ρ uni = Uniᵉπ c uni 
    Uni-⟦⟧s (γ ⊙ δ) ρ uni = Uni-⟦⟧s γ (⟦ δ ⟧s ρ) (Uni-⟦⟧s δ ρ uni)
    Uni-⟦⟧s (γ [ x ↦ M ]) ρ uni = ( Uni-⟦⟧s γ ρ uni , Uni-⟦⟧t M ρ uni )


  -- Eq(⟦M⟧ρ₁,⟦M⟧ρ₂) and Eq(⟦γ⟧ρ₁,⟦γ⟧ρ₂), if Eq(ρ₁,ρ₂)
    Eq-⟦⟧t-compat : ∀ {w Γ A} (M : Γ ⊢ A) {ρ₁ ρ₂} (uρ₁ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ₁)(uρ₂ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ₂) (eq : Eq⟨ w ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ])
                              → Eq⟨ w ⊩ A ⟩[ ⟦ M ⟧t ρ₁ , ⟦ M ⟧t ρ₂ ]
    -- Γ ∋ x ↳ occ
    Eq-⟦⟧t-compat {w} {Γ} [ .Γ ∋ x ↳ occ ] uρ₁ uρ₂ eq = Eq-cong-lookup eq occ
    -- ∶λ x # f ⇨ M
    Eq-⟦⟧t-compat {w} {Γ} {A ⇒ B} (∶λ x # f ⇨ M) uρ₁ uρ₂ eq = 
           λ {w'} c {v} uv → Eq-⟦⟧t-compat M 
                                                             (Uniᵉ↑ Γ c uρ₁ , uv) 
                                                             (Uniᵉ↑ Γ c uρ₂ , uv) 
                                                             ((  Eqᵉ-cong-↑{Γ} w' c eq , Eq-refl A _))  --
    -- M ⋆ N
    -- Eq-⟦⟧t-compat M eq  gives eq v, apply, can get     ⟦M⟧t ρ₁ (⟦N⟧ ρ₁) = ⟦M⟧t ρ₁ (⟦N⟧ ρ₂)  by uniformity of ⟦M⟧t ρ₁ , Eq-compat, uniformity of ⟦N⟧t 
    --                                                            can also get  ⟦M⟧t ρ₁ (⟦N⟧ ρ₂) = ⟦M⟧t ρ₂ (⟦N⟧ ρ₂)  by Eq-compat of  ⟦M⟧t , uniformity of ⟦N⟧t ρ₂
    Eq-⟦⟧t-compat {w} {Γ} {B} (M ⋆ N) uρ₁ uρ₂ eq = 
             Eq-trans B  ((Σ.proj₁ (Σ.proj₂ (Uni-⟦⟧t M _ uρ₁))) P.refl (Uni-⟦⟧t N _ uρ₁) (Uni-⟦⟧t N _ uρ₂) (Eq-⟦⟧t-compat N uρ₁ uρ₂ eq) ) 
                               ((Eq-⟦⟧t-compat M uρ₁ uρ₂ eq) P.refl (Uni-⟦⟧t N _ uρ₂)) 
    -- M ⟨ γ ⟩
    Eq-⟦⟧t-compat (M ⟨ γ ⟩) uρ₁ uρ₂ eq = Eq-⟦⟧t-compat M (Uni-⟦⟧s γ _ uρ₁) (Uni-⟦⟧s γ _ uρ₂) (Eq-⟦⟧s-compat γ uρ₁ uρ₂ eq) 

    Eq-⟦⟧s-compat :  ∀ {Δ Γ w} (γ : Δ ⇛ Γ) { ρ₁ ρ₂} (uρ₁ : Uni⟨ w ⊩ᵉ Δ ⟩ ρ₁) (uρ₂ : Uni⟨ w ⊩ᵉ Δ ⟩ ρ₂) (eq : Eq⟨ w ⊩ᵉ Δ ⟩[ ρ₁ , ρ₂ ])
                              → Eq⟨ w ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s ρ₁ , ⟦ γ ⟧s ρ₂ ]
    Eq-⟦⟧s-compat (π c) uρ₁ uρ₂ eq = Eqᵉ-cong-πᵉ c eq
    Eq-⟦⟧s-compat (γ ⊙ δ) uρ₁ uρ₂ eq = Eq-⟦⟧s-compat γ (Uni-⟦⟧s δ _ uρ₁) (Uni-⟦⟧s δ _ uρ₂) (Eq-⟦⟧s-compat δ uρ₁ uρ₂ eq)
    Eq-⟦⟧s-compat (γ [ x ↦ M ]) uρ₁ uρ₂ eq = (Eq-⟦⟧s-compat γ uρ₁ uρ₂ eq , Eq-⟦⟧t-compat M uρ₁ uρ₂ eq)




    -- Eq(↑c(⟦M⟧ρ), ⟦M⟧↑c(ρ))   and     Eq(↑c(⟦γ⟧ρ), ⟦γ⟧↑c(ρ))
    -- may require uniformity of ρ. Not a big problem as is guaranteed the only place it is used (in Uni-⟦⟧t)
    Eq-⟦⟧t↑-coherence : ∀ {Γ A}(M : Γ ⊢ A){w w'}(ρ : w ⊩ᵉ Γ)(uρ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) (c : w' ≥ʷ w)
                                    → Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]⟨ ⟦ M ⟧t ρ ⟩ , ⟦ M ⟧t ↑ᵉ[ c , Γ ]⟨ ρ ⟩ ]

    -- [ .Γ ∋ x ↳ occ ]
    Eq-⟦⟧t↑-coherence {Γ} [ .Γ ∋ x ↳ occ ] ρ _ c = Eq↑-lookup c ρ occ
    -- (∶λ x # f ⇨ M)
    Eq-⟦⟧t↑-coherence {Γ} {A ⇒ B} (∶λ x # f ⇨ M) ρ uρ c = 
       λ {w''} c' {v} uv → Eq-⟦⟧t-compat M (Uniᵉ↑ Γ (P.trans c' c) uρ , uv) 
                                        (Uniᵉ↑ Γ c' (Uniᵉ↑ Γ c uρ) , uv) 
                                        ( Eqᵉ-sym Γ (Eqᵉ↑↑ Γ c' c (P.trans c' c)) , Eq-refl A _ ) -- Eqᵉ↑↑
    -- (M ⋆ N)
    -- use eq-coherence-app↑, Eq↑↑ w/ refl∘c = c∘refl, possibly Eq↑-id (to add refl)
    -- but also requires coherence due to uniformity of (⟦M⟧t ρ), 
    -- so add uni ρ to argument. 
    -- outline. ↑c(Mρ refl Nρ) = ↑refl(Mp) c ↑c(Nρ) = (Mp) c ↑c(Nρ) = ↑c(Mρ) refl ↑c(Nρ) = M↑c(ρ) refl N↑c(ρ)
    Eq-⟦⟧t↑-coherence {Γ} {B} (_⋆_ {.Γ} {A} {.B} M N) ρ uρ c = 
                   Eq-trans B (((Σ.proj₂ (Σ.proj₂ (Uni-⟦⟧t M ρ uρ))) P.refl c c (Uni-⟦⟧t N ρ uρ)) ) 
                        (Eq-trans B 
                              (Eq-coherence-app↑ {_} {A} {B} (⟦ M ⟧t ρ) c) 
                              (Eq-cong-app {A} {B} P.refl 
                                (Uni↑ (A ⇒ B) c _ (Uni-⟦⟧t M ρ uρ)) 
                                (Uni-⟦⟧t M _ (Uniᵉ↑ Γ c uρ)) 
                                ((Uni↑ A c _ (Uni-⟦⟧t N ρ uρ))) 
                                ((Uni-⟦⟧t N _ (Uniᵉ↑ Γ c uρ)) ) 
                                (Eq-⟦⟧t↑-coherence M ρ uρ c) (Eq-⟦⟧t↑-coherence N ρ uρ c)))
    -- M ⟨ γ ⟩
    Eq-⟦⟧t↑-coherence {Δ} {A} (_⟨_⟩ {.Δ} {Γ} {.A} M γ) ρ uρ c = 
                      Eq-trans A (Eq-⟦⟧t↑-coherence M (⟦ γ ⟧s ρ) (Uni-⟦⟧s γ _ uρ ) c)
                                 (Eq-⟦⟧t-compat M (Uniᵉ↑ Γ c (Uni-⟦⟧s γ ρ uρ)) (Uni-⟦⟧s γ _ (Uniᵉ↑ Δ c uρ)) 
                                                 (Eq-⟦⟧s↑-coherence γ ρ uρ c))

    Eq-⟦⟧s↑-coherence : ∀ {Δ Γ}(γ : Δ ⇛ Γ){w w'}(ρ : w ⊩ᵉ Δ)(uρ : Uni⟨ w ⊩ᵉ Δ ⟩ ρ)(c : w' ≥ʷ w)
                                      → Eq⟨ w' ⊩ᵉ Γ ⟩[ ↑ᵉ[ c , Γ ]⟨ ⟦ γ ⟧s ρ ⟩ , ⟦ γ ⟧s ↑ᵉ[ c , Δ ]⟨ ρ ⟩ ]
    -- π c
    Eq-⟦⟧s↑-coherence {Δ} {Γ} (π c) ρ uρ c' = Eqᵉ↑π Γ _ c' c
    -- γ ⊙ δ
    Eq-⟦⟧s↑-coherence {Θ} {Δ} (_⊙_ {.Θ} {Γ} {.Δ} γ δ) ρ uρ c = 
                      Eqᵉ-trans Δ (Eq-⟦⟧s↑-coherence γ _ (Uni-⟦⟧s δ ρ uρ) c) 
                                  (Eq-⟦⟧s-compat γ (Uniᵉ↑ Γ c (Uni-⟦⟧s δ ρ uρ)) 
                                                 (Uni-⟦⟧s δ _ (Uniᵉ↑ Θ c uρ)) 
                                                 (Eq-⟦⟧s↑-coherence δ ρ uρ c))
    -- γ [ x ↦ M ]
    Eq-⟦⟧s↑-coherence (γ [ x ↦ M ]) ρ uρ c = (Eq-⟦⟧s↑-coherence γ ρ uρ c , Eq-⟦⟧t↑-coherence M ρ uρ c)



  -- Theorem 4: M,N ∈ Γ ⊢ A; M≅N; ρ ∈ w ⊩ᵉ Γ → Eq(⟦M⟧ρ,⟦N⟧ρ)
  -- proof of both by induction on the proof of conversion.
  mutual 
    theorem₄ : ∀ {Γ A w} (M N : Γ ⊢ A)(MN : Γ ⊢ A ∋ M ≅ N)(ρ : w ⊩ᵉ Γ)(uρ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) 
         → Eq⟨ w ⊩ A ⟩[ ⟦ M ⟧t ρ , ⟦ N ⟧t ρ ]
    theorem₄ {Γ} {A} .N N refl ρ uρ = Eq-refl A _
    theorem₄ {Γ} {A} M N (lstep {.M} {M'} {.N} p₁ p₂) ρ uρ = Eq-trans A (theorem₄-≐ M M' p₁ ρ uρ) (theorem₄ M' N p₂ ρ uρ)
    theorem₄ {Γ} {A} M N (rstep {.M} {M'} {.N} p₁ p₂) ρ uρ = Eq-trans A (Eq-sym A (theorem₄-≐ M' M p₁ ρ uρ))
                                                                      (theorem₄ M' N p₂ ρ uρ) 

    -- Fun thought. Seems that sub-occurrence for rules should be ≅ , not ≐. and that def of ≅ is wrong.
    -- but because the relation is a congruence, the naive sym refl trans closure does the right thing. 
    theorem₄-≐ : ∀ {Γ A w} (M N : Γ ⊢ A)(MN : Γ ⊢ A ∋ M ≐ N)(ρ : w ⊩ᵉ Γ)(uρ : Uni⟨ w ⊩ᵉ Γ ⟩ ρ) 
         → Eq⟨ w ⊩ A ⟩[ ⟦ M ⟧t ρ , ⟦ N ⟧t ρ ]
    -- cλ (congruence for ∶λ x ⇨ M)
    theorem₄-≐ {Γ} .(∶λ x # f ⇨ M) .(∶λ x # f ⇨ N) (cλ {.Γ} {x} {f} {A} {B} {M} {N} r) ρ uρ = 
                 λ c uv → theorem₄-≐ M N r _ ((Uniᵉ↑ Γ c uρ , uv))      
    -- ca₁ (congruence for app on left side)
    theorem₄-≐ {Γ} {B} .(M ⋆ P) .(N ⋆ P) (ca₁ {.Γ} {A} {.B} {M} {N} {P} r) ρ uρ = 
                 (theorem₄-≐ M N r ρ uρ) P.refl (Uni-⟦⟧t P ρ uρ) 
    -- ca₂ (congruence for app on left side)
    theorem₄-≐ {Γ} {B} .(M ⋆ P) .(M ⋆ Q) (ca₂ {.Γ} {A} {.B} {M} {P} {Q} r) ρ uρ = 
                 Eq-cong-app {A} {B} P.refl (Uni-⟦⟧t M ρ uρ) (Uni-⟦⟧t M ρ uρ) (Uni-⟦⟧t P ρ uρ) (Uni-⟦⟧t Q ρ uρ) (Eq-refl (A ⇒ B) (⟦ M ⟧t ρ)) (theorem₄-≐ P Q r ρ uρ)
    -- cs₁ (congruence esubst term on lhs)
    theorem₄-≐ {Γ} {A} .(M ⟨ γ ⟩) .(N ⟨ γ ⟩) (cs₁ {Γ'} {.Γ} {.A} {M} {N} {γ} r) ρ uρ = 
                 theorem₄-≐ M N r ( ⟦ γ ⟧s ρ ) (Uni-⟦⟧s γ ρ uρ)
    -- cs₂ (congruence esubst term on lhs)
    theorem₄-≐ {Γ} {A} .(M ⟨ γ₁ ⟩) .(M ⟨ γ₂ ⟩) (cs₂ {Γ'} {.Γ} {.A} {M} {γ₁} {γ₂} r) ρ uρ = 
                Eq-⟦⟧t-compat M (Uni-⟦⟧s γ₁ ρ  uρ) (Uni-⟦⟧s γ₂ ρ  uρ) (th₄ˢ-≐ γ₁ γ₂ r ρ uρ) 
    -- :β  
    theorem₄-≐ {Γ} {A} .(((∶λ x # f ⇨ M) ⟨ γ ⟩) ⋆ N) .(M ⟨ γ [ x ↦ N ] ⟩) (:β {x} {Γ'} {.Γ} {f} {γ} {A'} {.A} {M} {N}) ρ uρ = 
                Eq-⟦⟧t-compat M ( Uniᵉ↑ Γ' P.refl (Uni-⟦⟧s γ ρ uρ) , Uni-⟦⟧t N ρ uρ )
                                          (Uni-⟦⟧s γ ρ uρ , Uni-⟦⟧t N ρ uρ )
                                          (Eqᵉ↑-id Γ' P.refl , Eq-refl A' _)
    -- :η 
    --    ⟦ M ⟧t (πᵉ c (↑ᵉ[ c' , Γ ]⟨ ρ ⟩ , v))  refl  v        (i.e. ⟦ ∶λ x # f ⇨ ((M ⟨ π c ⟩) ⋆ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟧
    --    =  (⟦ M ⟧t ↑ᵉ[ c' , Γ ]⟨ ρ ⟩)   refl  v
    --    = ↑[ c' , A ⇒ B ]⟨ ⟦ M ⟧t ρ ⟩  refl v
    --    = (⟦ M ⟧t ρ) c' v                                           (i.e. ⟦ M ⟧
    theorem₄-≐ {Γ} {A ⇒ B} {w} M .(∶λ x # f ⇨ ((M ⟨ π c ⟩) ⋆ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ])) (:η {.Γ} {.A} {.B} {x} {f} .M {c}) ρ uρ = 
               λ {w'} c' {v} uv → 
                      Eq-sym B {w'} 
                          (Eq-trans B {w'} {⟦ M ⟧t (πᵉ c (↑ᵉ[ c' , Γ ]⟨ ρ ⟩ , v)) P.refl v} { (⟦ M ⟧t ↑ᵉ[ c' , Γ ]⟨ ρ ⟩) P.refl  v} {(⟦ M ⟧t ρ) c' v}
                               (Eq-cong-app {A} {B} P.refl 
                                      (Uni-⟦⟧t M _ (Uniᵉπ c (Uniᵉ↑ Γ c' uρ , uv))) (Uni-⟦⟧t M _ (Uniᵉ↑ Γ c' uρ )) 
                                      uv uv 
                                      (Eq-⟦⟧t-compat M (Uniᵉπ c (Uniᵉ↑ Γ c' uρ , uv)) (Uniᵉ↑ Γ c' uρ) (Eqᵉ-trans Γ (Eqπ-step {w'} (lemma₃ {Γ}) c)
                                                                                                   (Eqπ-id Γ lemma₃))) 
                                      (Eq-refl A v))
                               (Eq-trans B {w'} {(⟦ M ⟧t ↑ᵉ[ c' , Γ ]⟨ ρ ⟩) P.refl  v} {↑[ c' , A ⇒ B ]⟨ ⟦ M ⟧t ρ ⟩ P.refl v} {(⟦ M ⟧t ρ) c' v}
                                      (Eq-cong-app {A} {B} {w'} {w'} P.refl (Uni-⟦⟧t M _ (Uniᵉ↑ Γ c' uρ)) (Uni↑ (A ⇒ B) c' _ (Uni-⟦⟧t M _ uρ)) uv uv 
                                               (Eq-sym (A ⇒ B) {w'} (Eq-⟦⟧t↑-coherence M {w} {w'} ρ uρ c' ))   -- 
                                               (Eq-refl A v)) 
                                      (Eq-sym B (Eq-coherence-app↑ {w} {A} {B} (⟦ M ⟧t ρ) {w'}  c' {v}) )))
    -- lookup of x in subst extended with x reduces to refl
    theorem₄-≐ {Γ} {A} .([ Γ' ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟨ γ [ x ↦ N ] ⟩) N (:v₁ {Γ'} {.Γ} {.A} {x} {f} {.N} {γ}) ρ uρ = Eq-refl A _
    -- meaning of var invariant across weakenings. 
    theorem₄-≐ {Δ} {A} .([ Γ ∋ x ↳ inΓ ] ⟨ π c ⟩) .([ Δ ∋ x ↳ inΔ ]) (:v₂ {Γ} {.Δ} {x} {.A} {inΓ} {inΔ} {c}) ρ uρ = Eq-sym A (Eq-lookup c inΔ inΓ) 
    -- explicit subst with id weakening is same as unsubstituted term.
    theorem₄-≐ {Γ} {A} .(N ⟨ π c ⟩) N (:sid {.Γ} {.A} {c}) ρ uρ = Eq-⟦⟧t-compat N (Uniᵉπ c uρ) uρ (Eqπ-id Γ c)
    -- unrolling of definitions proves app subst law by refl
    theorem₄-≐ {Γ} {A} .((M ⋆ N) ⟨ γ ⟩) .((M ⟨ γ ⟩) ⋆ (N ⟨ γ ⟩)) (:sapp {Γ'} {.Γ} {γ} {A'} {.A} {M} {N}) ρ uρ = Eq-refl A _
    -- same for composition.
    theorem₄-≐ {Γ} {A} .((M ⟨ γ ⟩) ⟨ δ ⟩) .(M ⟨ γ ⊙ δ ⟩) (:s⊙ {.Γ} {Γ'} {Δ} {.A} {δ} {γ} {M}) ρ uρ = Eq-refl A _


    th₄ˢ : ∀ {Δ Γ w} (γ δ : Δ ⇛ Γ)(γδ : Δ ⊢ Γ ∋ γ ≅ˢ δ)(ρ : w ⊩ᵉ Δ)(uρ : Uni⟨ w ⊩ᵉ Δ ⟩ ρ)  
         → Eq⟨ w ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s ρ , ⟦ δ ⟧s ρ ]
    th₄ˢ {Δ} {Γ} .δ δ refl ρ uρ = Eqᵉ-refl Γ _
    th₄ˢ {Δ} {Γ} γ δ (lstep {.γ} {γ'} {.δ} p₁ p₂) ρ uρ = Eqᵉ-trans Γ (th₄ˢ-≐ γ γ' p₁ ρ uρ) (th₄ˢ γ' δ p₂ ρ uρ)
    th₄ˢ {Δ} {Γ} γ δ (rstep {.γ} {γ'} {.δ} p₁ p₂) ρ uρ = Eqᵉ-trans Γ (Eqᵉ-sym Γ (th₄ˢ-≐ γ' γ p₁ ρ uρ))
                                                                                        (th₄ˢ γ' δ p₂ ρ uρ)



    th₄ˢ-≐ : ∀ {Δ Γ w} (γ δ : Δ ⇛ Γ)(γδ : Δ ⊢ Γ ∋ γ ≐ˢ δ)(ρ : w ⊩ᵉ Δ)(uρ : Uni⟨ w ⊩ᵉ Δ ⟩ ρ)  
         → Eq⟨ w ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s ρ , ⟦ δ ⟧s ρ ]
    th₄ˢ-≐  {Ψ} {Γ} .(δ₁ ⊙ γ) .(δ₂ ⊙ γ) (c∘₁ {.Ψ} {Δ} {.Γ} {δ₁} {δ₂} {γ} r) ρ uρ = th₄ˢ-≐ δ₁ δ₂ r _ (Uni-⟦⟧s γ _ uρ )
    th₄ˢ-≐  {Ψ} {Γ} .(δ ⊙ γ₁) .(δ ⊙ γ₂) (c∘₂ {.Ψ} {Δ} {.Γ} {δ} {γ₁} {γ₂} r) ρ uρ  = 
            Eq-⟦⟧s-compat  δ (Uni-⟦⟧s γ₁ _ uρ) (Uni-⟦⟧s γ₂ _ uρ) (th₄ˢ-≐ γ₁ γ₂ r ρ uρ)
    th₄ˢ-≐  {Δ} {Γ ∙[ x ∶ A ]⊣ f } .(γ₁ [ x ↦ M ]) .(γ₂ [ x ↦ M ]) (c≔₁ {.Δ} {.Γ} {γ₁} {γ₂} {.A} {.x} {.f} {M} r) ρ uρ = 
            (th₄ˢ-≐ γ₁ γ₂ r ρ uρ , Eq-refl A _)
    th₄ˢ-≐  {Δ} {Γ ∙[ x ∶ A ]⊣ f } .(γ [ x ↦ M ]) .(γ [ x ↦ N ]) (c≔₂ {.Δ} {.Γ} {γ} {.A} {.x} {.f} {M} {N} r) ρ uρ = 
            (Eqᵉ-refl Γ _ , theorem₄-≐ M N r ρ uρ)
    th₄ˢ-≐  {Θ} {Ω} .((γ ⊙ δ) ⊙ θ) .(γ ⊙ (δ ⊙ θ)) (⊙-assoc {.Θ} {Δ} {Γ} {.Ω} {γ} {δ} {θ}) ρ uρ = Eqᵉ-refl Ω _
    th₄ˢ-≐  {Θ} {Γ ∙[ x ∶ A ]⊣ f} .((γ [ x ↦ M ]) ⊙ δ) .((γ ⊙ δ) [ x ↦ M ⟨ δ ⟩ ]) (∶ext∶⊙ {.Θ} {Δ} {.Γ} {.A} {γ} {.x} {δ} {.f} {M}) ρ uρ =
            (Eqᵉ-refl Γ _ , Eq-refl A _)
    th₄ˢ-≐  {Δ} {Γ} .((π c) ⊙ (δ [ x ↦ M ])) δ (∶π∶ext {.Δ} {.Γ} {A} {x} {f} {.δ} {M} {c}) ρ uρ = 
            (Eqᵉ-trans Γ (Eqπ-step (lemma₃ {Γ}) c) (Eqπ-id Γ lemma₃))
    th₄ˢ-≐  {Θ} {Γ} .((π c₁) ⊙ (π c₂)) .(π c₃) (∶⊙∶π {.Θ} {Δ} {.Γ} {c₂} {c₁} {c₃}) ρ uρ = Eqππ Γ Δ Θ c₁ c₂ c₃
    th₄ˢ-≐  {Δ} {Γ} .(δ ⊙ (π c)) δ (:πid {.Δ} {.Γ} {.δ} {c}) ρ uρ = Eq-⟦⟧s-compat δ (Uniᵉπ c uρ) uρ (Eqπ-id Δ c)
    th₄ˢ-≐  {Γ} {ε} γ .(π c) (:πε {.Γ} {.γ} {c}) ρ uρ = tt
    th₄ˢ-≐  {Δ} {Γ ∙[ x ∶ A ]⊣ f} γ .(((π c) ⊙ γ) [ x ↦ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ occ ] ⟨ γ ⟩ ]) (:ηε {.Δ} {.Γ} {.A} .x {.f} occ .γ c) ρ uρ with (⟦ γ ⟧s ρ) 
    th₄ˢ-≐ {Δ} {Γ ∙[ x ∶ A ]⊣ f} γ .(((π c) ⊙ γ) [ x ↦ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! {Γ} {f} ] ⟨ γ ⟩ ]) (:ηε .x here! .γ c) ρ uρ | ρ' , v =  Eqᵉ-sym Γ (Eqᵉ-trans Γ (Eqπ-step (lemma₃ {Γ}) c) (Eqπ-id Γ lemma₃)) , Eq-refl A _
    th₄ˢ-≐ {Δ} {Γ ∙[ x ∶ A ]⊣ f} γ .(((π c) ⊙ γ) [ x ↦ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ there {x} {A} {Γ} f occ ] ⟨ γ ⟩ ]) (:ηε .x (there .f occ) .γ c) ρ uρ | ρ' , v = ⊥-elim (refuteFresh f occ)
--- End of module KSem   (Kripke semantics for terms)
