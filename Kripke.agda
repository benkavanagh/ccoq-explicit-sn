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

  -- subst(simplified).  (P : A → Set)  →  P  Respects ≡
  --             i.e.           (P : A → Set)  →  x ≡ y → P x →  P y

  -- Eq↑: lifting by identity has no effect
  Eq↑ : ∀ A {w} u (c : w ≥ʷ w) → Eq⟨ w ⊩ A ⟩[ ↑[ c , A ]⟨ u ⟩ , u ]
  Eq↑ ♭ u c = λ c' → cong u (uniq≥ _ _)
  Eq↑ (A ⇒ B) {w} u c = 
        λ {w'} c' {v} uni-v → subst ((λ c → Eq⟨ w' ⊩ B ⟩[ u c v , u c' v ])) (uniq≥ _ _) (Eq-refl B _)

  
  -- Eq↑↑ :  repeated lifting equal to lifting by transitive order.    (again uniq≥)
  Eq↑↑ : ∀ A {w} u {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) →
         Eq⟨ w₂ ⊩ A ⟩[ ↑[ c₂ , A ]⟨ ↑[ c₁ , A ]⟨ u ⟩ ⟩ , ↑[ c₃ , A ]⟨ u ⟩ ]
  Eq↑↑ ♭ u c₁ c₂ c₃ = λ c → cong u (uniq≥ _ _)
  Eq↑↑ (A ⇒ B) {w} u {w₁} {w₂} c₁ c₂ c₃ = 
        λ {w' } c {v } uni-v → subst (λ c' → Eq⟨ w' ⊩ B ⟩[ u c' v , u (P.trans c c₃) v ]) (uniq≥ _ _) (Eq-refl B (u _ v))

  -- Eqapp↑    semantic application of u to value v at higher world w' is equal to  application of u lifted to w' to v (via refl)
  --                
  Eqapp↑ : ∀ {w B A} (u : w ⊩ A ⇒ B) {w'} (c : w' ≥ʷ w) {v} →
           Eq⟨ w' ⊩ B ⟩[ u c v , (↑[ c , A ⇒ B ]⟨ u ⟩) P.refl v ]
  Eqapp↑ {w} {B} u {w'} c {v} rewrite (uniq≥ (P.trans P.refl c) c) = Eq-refl B _ 


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
  Eq-lookup : ∀ {Γ Δ w ρ} (c : Γ ≥ Δ) {x A} (occ₁ : [ x ∶ A ]∈ Γ) (occ₂ : [ x ∶ A ]∈ Δ) →
              Eq⟨ w ⊩ A ⟩[ lookup Γ ρ occ₁ , lookup Δ (πᵉ c ρ) occ₂ ]
  Eq-lookup stop occ ()
  Eq-lookup {Γ} {Δ ∙[ x ∶ A ]⊣ f} {w} {ρ} (step c occ₁ .f) {.x} {.A} occ₂ here! = lookup-uniq ρ occ₂ occ₁
  Eq-lookup (step c occ f) pr (there .f pr') = Eq-lookup c pr pr' 

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

