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
open import PT
open import Kripke

calculus : Kripke
calculus = kripke Context _≥_ ≥-isPreorder lemma₇ (λ Γ → Γ ⊢ ♭)



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


