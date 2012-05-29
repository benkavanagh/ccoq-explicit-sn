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
import Level as Lvl

open import Closures

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

infix 10 _⊢_ _⇛_ 

-- M,N ::=  [Γ ⊧ x ↳ loc] |  ∶λ x ⇨ M  |  M ⋆ N  |  M 〈 σ 〉
mutual 
  data _⊢_ : (Γ : Context)(A : Type) → Set where
    [_⊧_↳_] : ∀ {A} Γ (x : Name) (occ :  [ x ∶ A ]∈ Γ) → Γ ⊢ A    -- var at occ location
    ∶λ_⇨_ : ∀{Γ A B} (x : Name)  {f : T(x # Γ)} (t : Γ ∙[ x ∶ A ]⊣ f ⊢ B) → Γ ⊢ A ⇒ B   -- lambda
    _⋆_ : ∀{Γ A B} → (e₁ : Γ ⊢ A ⇒ B) (e₂ : Γ ⊢ A) → Γ ⊢ B          -- apply
    _〈_〉 : ∀{Δ}{Γ}{A} → (Γ ⊢ A) → (Δ ⇛ Γ) → (Δ ⊢ A)   -- explicit subst

-- γ, δ ::= π c | γ ⊙ δ | γ [ x → M ]
  data _⇛_ : (Γ : Context)(Δ : Context) → Set where
    π_ : ∀{Δ}{Γ} → (Δ ≥ Γ) → (Δ ⇛ Γ)      -- project
    _⊙_ :  ∀{Θ}{Γ}{Δ} → (Γ ⇛ Δ) → (Θ ⇛ Γ) → (Θ ⇛ Δ)    -- compose
    _[_↦_] : ∀{Δ}{Γ}{A} → (Δ ⇛ Γ) → (x : Name) → {f : T(x # Γ)} → (Δ ⊢ A) → (Δ ⇛ (Γ ∙[ x ∶ A ]⊣ f))  -- update


-- ( _⊢_∋_≅_ )  =  (_⊢_∋_≐_)* 
data _⊢_∋_≐_ : ∀ Γ A  (M N : Γ ⊢ A) → Set where
  :β : ∀{x Γ Δ}{f : T(x # Γ)} {γ : Δ ⇛ Γ} {A B}{M : (Γ ∙[ x ∶ A ]⊣ f)  ⊢ B}{N : Δ ⊢ A} 
            → Δ ⊢ B ∋ (((∶λ x ⇨ M) 〈 γ 〉) ⋆ N) ≐ M 〈 γ [ x ↦ N ] 〉 
  :η : ∀ {Γ A B x} {f : T(x # Γ)} (M : (Γ ⊢ (A ⇒ B)))  { c } → Γ ⊢ A ⇒ B ∋ M  ≐ (∶λ x ⇨ ((M 〈 π c 〉) ⋆ [ (Γ ∙[ x ∶ A ]⊣ f) ⊧ x ↳ here! ])) 
  :v₁ : ∀{Γ A x} {f : T(x # Γ)} {M γ} →  (Γ ∙[ x ∶ A ]⊣ f) ⊢ A ∋ ([ (Γ ∙[ x ∶ A ]⊣ f) ⊧ x ↳ here! ] 〈 γ [ x  ↦ M ] 〉)  ≐  M 
  :v₂ : ∀{Γ Δ : Context} {x A inΓ inΔ} (c : Δ ≥ Γ) →   Δ ⊢ A ∋ ([ Γ ⊧ x ↳ inΓ ] 〈 π c 〉) ≐  [ Δ ⊧ x ↳ inΔ ] 
  :sid : ∀ {Γ A c M} → Γ ⊢ A ∋ M 〈 π c 〉 ≐ M 
  :sapp : ∀ {Γ Δ}{γ : Δ ⇛ Γ} {A B} {M : Γ ⊢ A ⇒ B}{N} → Δ ⊢ B ∋ (M ⋆ N) 〈 γ 〉 ≐  (M 〈 γ 〉 ⋆ N 〈 γ 〉)
  :s⊙ :  ∀{Θ Γ Δ A} {δ : Θ ⇛ Γ}{γ : Γ ⇛ Δ}{M : Δ ⊢ A} →  Θ ⊢ A ∋ M 〈 γ 〉 〈 δ 〉 ≐ M 〈 γ ⊙ δ 〉 

-- ( _⊢_∋_≅ˢ_ ) = (_⊢_∋_≐ˢ_ )* 
data _⊢_∋_≐ˢ_ : ∀ Δ Γ  (γ δ : Δ ⇛ Γ) → Set where
  ⊙-assoc : ∀{Γ Δ Θ Ω}{γ : Γ ⇛ Ω}{δ : Δ ⇛ Γ}{θ : Θ ⇛ Δ } → Θ ⊢ Ω ∋ ((γ ⊙ δ) ⊙ θ) ≐ˢ (γ ⊙ (δ ⊙ θ))
  ∶ext∶⊙ : ∀{Γ A Δ Θ}(γ : Δ ⇛ Γ) (x : Name) (δ : Θ ⇛ Δ) {f : T(x # Γ)} (M : Δ ⊢ A) 
         → Θ ⊢ (Γ ∙[ x ∶ A ]⊣ f) ∋ (γ [ x ↦ M ] ⊙ δ) ≐ˢ ((γ ⊙ δ) [ x ↦ M 〈 δ 〉 ])
  ∶π∶ext : ∀{Γ Δ A}(x : Name){f : T(x # Γ)}(γ : Δ ⇛ Γ)(M : Δ ⊢ A)(c : (Γ ∙[ x ∶ A ]⊣ f)  ≥ Γ) 
         → Δ ⊢ Γ ∋ (π c ⊙ (γ [ x ↦ M ])) ≐ˢ  γ
  ∶⊙∶π  :  ∀{Θ Δ}{Γ}(c₂ : Θ ≥ Δ)(c₁ : Δ ≥ Γ)(c₃ : Θ ≥ Γ) → Θ ⊢ Γ ∋ (π c₁ ⊙ π c₂)  ≐ˢ (π c₃)
  :πid :  ∀{Γ Δ} (γ : Γ ⇛ Δ)(c : Γ ≥ Γ) → Γ ⊢ Δ ∋ (γ ⊙ π c) ≐ˢ γ
  :πε :  ∀{Γ}(γ : Γ ⇛ ε)(c : Γ ≥ ε) → Γ ⊢ ε ∋ γ ≐ˢ (π c) 
  :ηε :  ∀{Γ Δ A}(x : Name) {f : T(x # Γ)} (occ : [ x ∶ A ]∈ (Γ ∙[ x ∶ A ]⊣ f)) (γ : Δ ⇛ (Γ ∙[ x ∶ A ]⊣ f)) (c : (Γ ∙[ x ∶ A ]⊣ f) ≥ Γ) 
         → Δ ⊢ (Γ ∙[ x ∶ A ]⊣ f) ∋ γ  ≐ˢ ((π c ⊙ γ) [ x ↦ [(Γ ∙[ x ∶ A ]⊣ f) ⊧ x ↳ occ ] 〈 γ 〉 ])

_⊢_∋_≅_ :  ∀ Γ A s t → Set
Γ ⊢ A ∋ s ≅ t = s ≡[ _⊢_∋_≐_ Γ A ]* t

_⊢_∋_≅ˢ_  : ∀ Γ Δ s t → Set
Γ ⊢ Δ ∋ s ≅ˢ t = s ≡[ _⊢_∋_≐ˢ_ Γ Δ ]* t

-- semantic objects

-- first define Kripke models
record Kripke {a} : Set (Lvl.suc a) where
   constructor kripke
   field 
     W : Set a
     _≥ʷ_ : Rel W a   -- partial order rel
     isPO : IsPartialOrder (_≡_{a}{W})  _≥ʷ_
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
  module P = IsPartialOrder isPO         -- adds fields of isPO to namespace of module

  infix 10 _⊩_

  -- semantic objects
  _⊩_ : (w : W)(A : Type) → Set
  w ⊩ ♭ = {w' : W}(ge : w' ≥ʷ w) → G w'
  w ⊩ (A ⇒ B) = {w' : W} (ge : w' ≥ʷ w) (h : w' ⊩ A) → w' ⊩ B 

-- elimination rules for witnesses of forcing.... These give witnesses at future worlds.
-- TODO: give these appropriate infix syntax so there use below in Eq, Uni is apparent.
  ground : ∀{w' w} → (f : w ⊩ ♭) (ge : w' ≥ʷ w) → G w'
  ground f ge = f ge

  app : ∀{w' A w B}(fc : w ⊩ (A ⇒ B)) (ge : w' ≥ʷ w) (fcA : w' ⊩ A) → (w' ⊩ B)
  app f ge f' = f ge f' 

  ↑[_,_]〈_〉  : ∀ {w w'} (ge : w' ≥ʷ w) A (u : w ⊩ A) → w' ⊩ A
  ↑[ c , ♭ ]〈 u 〉 = λ inc → u (P.trans inc c)
  ↑[ c , A ⇒ B ]〈 u 〉 = λ inc → u (P.trans inc c)


  mutual
   
    -- Eq and Uni are mutually defined, binary and unary predicates over semantic objects u, v ∈ w ⊩ A
   
    -- Eq: two semantic objects at ground type are equal if they give the same element at all future worlds,
    --   and at function type if under application they map all uniform semantic objects to equal semantic objects                
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
        Eq⟨ w₂ ⊩ B ⟩[ ↑[ c₂ , B ]〈 u c₁ v 〉 , u c₃ (↑[ c₂ , A ]〈 v 〉) ])


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


  Eq-cong-app : ∀ A B {w w'} (c : w' ≥ʷ w)  (u u' : w ⊩ A ⇒ B) (v v' : w' ⊩ A) (eq₁ : Eq⟨ w ⊩ A ⇒ B ⟩[ u , u' ]) (eq₂ : Eq⟨ w' ⊩ A ⟩[ v , v' ]) →
              Eq⟨ w' ⊩ B ⟩[ u c v , u' c v' ]
  Eq-cong-app ♭ ♭ {w} {w'} c u u' v v' eq1 eq2 = λ c' → eqr c'
     where 
     eqr : {w'' : W} (c' : w'' ≥ʷ w') → (u c v c' ≡ u' c v' c')
     eqr c' rewrite (eq1 c {v} _ c') = {!!}
  Eq-cong-app ♭ (S ⇒ T) c u u' v v' eq1 eq2 = {!!}
  Eq-cong-app (S ⇒ T) B c u u' v v' eq1 eq2 = {!!}


  Eq-cong-↑ : ∀ A {w w' : W} (c : w' ≥ʷ w) u u' (eq₁ : Eq⟨ w ⊩ A ⟩[ u , u' ])  → Eq⟨ w' ⊩ A ⟩[ ↑[ c , A ]〈 u 〉 , ↑[ c , A ]〈 u' 〉 ] 
  Eq-cong-↑ A c u u' eq = {!!}

  ↑Uni-endo : ∀ A {w w' : W} (c : w' ≥ʷ w) u (uni : Uni⟨ w ⊩ A ⟩ u) → Uni⟨ w' ⊩ A ⟩ (↑[ c , A ]〈 u 〉)
  ↑Uni-endo A c u uni = {!!}


  -- 
  Eq↑ : ∀ A {w} u (c : w ≥ʷ w) → Eq⟨ w ⊩ A ⟩[ ↑[ c , A ]〈 u 〉 , u ]
  Eq↑ ♭ u c = λ c' → cong u (uniq≥ _ _)
  Eq↑ (A ⇒ B) {w} u c = f   
     where 
       f :  {w' : W} (c' : w' ≥ʷ w) {v : w' ⊩ A} → Uni⟨ w' ⊩ A ⟩ v → Eq⟨ w' ⊩ B ⟩[ ↑[ c , A ⇒ B ]〈 u 〉 c' v , u c' v ]
       f c' u' rewrite (uniq≥ (P.trans c' c) c') = Eq-refl B _


{-  Method using subst by G.Allais.  subst allows you to substitute values of ≡ type.   
  Eq↑ : ∀ A {w} u (c : w ≥ʷ w) → Eq⟨ w ⊩ A ⟩[ ↑[ c , A ]〈 u 〉 , u ]
  Eq↑ ♭ u c = λ c' → cong u (uniq≥ _ c')
  Eq↑ (A ⇒ B) u c =
  -- cast
    λ {w'} c' {v} uni' → subst (λ c → Eq⟨ w' ⊩ B ⟩[ u c v , u c' v ]) (uniq≥ c' _)
  -- actual proof
    (Eq-refl B (u c' v))
-}
  
  Eq↑↑ : ∀ A {w} u {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) →
         Eq⟨ w₂ ⊩ A ⟩[ ↑[ c₂ , A ]〈 ↑[ c₁ , A ]〈 u 〉 〉 , ↑[ c₃ , A ]〈 u 〉 ]
  Eq↑↑ ♭ u c₁ c₂ c₃ = λ c → cong u (uniq≥ _ _)
  Eq↑↑ (A ⇒ B) {w} u {w₁} {w₂} c₁ c₂ c₃ = f
    where 
      f : ∀ {w' : W} (c : w' ≥ʷ w₂) {v : w' ⊩ A} → Uni⟨ w' ⊩ A ⟩ v → Eq⟨ w' ⊩ B ⟩[ ↑[ c₂ , A ⇒ B ]〈 ↑[ c₁ , A ⇒ B ]〈 u 〉 〉 c v ,
                                                                                                                   ↑[ c₃ , A ⇒ B ]〈 u 〉 c v ] 
      f c u rewrite (uniq≥ (P.trans (P.trans c c₂) c₁) (P.trans c c₃)) = Eq-refl B _

{- subst version.
  Eq↑↑ : ∀ A {w} u {w₁ w₂} (c₁ : w₁ ≥ʷ w) (c₂ : w₂ ≥ʷ w₁) (c₃ : w₂ ≥ʷ w) →
         Eq⟨ w₂ ⊩ A ⟩[ ↑[ c₂ , A ]〈 ↑[ c₁ , A ]〈 u 〉 〉 , ↑[ c₃ , A ]〈 u 〉 ]
  Eq↑↑ ♭ u c₁ c₂ c₃ = λ c → cong u (uniq≥ _ _)
  Eq↑↑ (A ⇒ B) u c₁ c₂ c₃ = 
  -- cast
    λ {w'} c' {v} uni' → subst (λ c → Eq⟨ w' ⊩ B ⟩[ u c v , u (P.trans c' c₃) v ]) (uniq≥ _ _)
  -- actual proof
    (Eq-refl B (u _ v))
-}

  Eqapp↑ : ∀ {w B A} (u : w ⊩ A ⇒ B) {w'} (c : w' ≥ʷ w) {v} →
           Eq⟨ w' ⊩ B ⟩[ u c v , (↑[ c , A ⇒ B ]〈 u 〉) P.refl v ]
  Eqapp↑ {w} {B} u {w'} c {v} rewrite (uniq≥ (P.trans P.refl c) c) = Eq-refl B _ 

{- subst version.
  Eqapp↑ : ∀ {w B A} (u : w ⊩ A ⇒ B) {w'} (c : w' ≥ʷ w) {v} →
           Eq⟨ w' ⊩ B ⟩[ u c v , (↑[ c , A ⇒ B ]〈 u 〉) P.refl v ]
  Eqapp↑ {w} {B} u {w'} c {v} =
    subst (λ c' → Eq⟨ w' ⊩ B ⟩[ u c v , u c' v ]) (uniq≥ _ _) (Eq-refl B (u c v))
-}

-- semantic environments. 
  data _⊪_ : (w ∈ W) (Γ : Context) → Set where
    εʷ : ∀ {w} → w ⊪ ε
    ⟨_∙_⟩ : ∀ {w x} (ρ : w ⊪ Γ) (v : w ⊩ A) → w ⊪ Γ ∙[ x ∶ A ]⊣ f
  


-- next. 1. define the boring lemmas. 
--          2. define evaluation / reify. 
--          3. more!

