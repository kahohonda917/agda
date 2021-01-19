module lemma1 where

open import DSt
open import CPSt

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality




subst-cont  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  --{t : var τ₃ → cpsvalue[ var ] (cpsM μα)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  --cpsSubstVal (λ x → t x) v t′ →
  cpsSubst (λ x → k₁ x (v₁ x) (t′)) v (k₂ v₁′ t′)


-- subst-trail  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
--               (t₁ : var τ₃ → cpsvalue[ var ] (cpsM μα)) →
--               (v : cpsvalue[ var ] τ₃) →
--               (t₂ : cpsvalue[ var ] (cpsM μα)) → Set

-- subst-trail {var} {τ₁} {τ₂} {∙} {τ₃} t₁ v t₂ = cpsSubst (λ x → CPSVal CPSId) v (CPSVal CPSId)
-- subst-trail {var} {τ₁} {τ₂} {x ⇒ x₁ , μα} {τ₃} t₁ v t₂ = {!!}
  -- {k : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
  --              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  -- {k′ : cpsvalue[ var ] (cpsT τ₁) →
  --              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  -- {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  -- {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  -- cpsSubst (λ x → k x v₁′ t₂) v (k′ v₁′ t₂) →
  -- cpsSubstVal (λ x → v₁ x) v v₁′ →
  -- cpsSubst (λ x → k′ v₁′ (t₁ x)) v (k′ v₁′ t₂)

mutual
  SubstV≠ : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSId} = sId
  SubstV≠ {var} {t = CPSTrail t} = sTra SubstV≠

  Subst≠  : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsterm[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp t t₁} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet t x} = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus t t₁} = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk x x₁ t} = sIdk SubstV≠ SubstV≠
  Subst≠ {t = CPSAppend x t t₁} = sApd Subst≠ Subst≠
  Subst≠ {t = CPSCons x t t₁} = sCon Subst≠ Subst≠

mutual

  SubstV-id  : {var : typ → Set}{τ₁ τ₂ : typ} →
               {v₁ : value[ var ] τ₁} →
               {v : value[ var ] τ₂} →
                SubstVal (λ _ → v₁) v v₁

  SubstV-id {var} {τ₁} {τ₂} {Var x} {v} = sVar≠
  SubstV-id {var} {.Nat} {τ₂} {Num n} {v} = sNum
  SubstV-id {var} {.(_ ⇒ _ ⟨ _ ⟩ _ ⟨ _ ⟩ _)} {τ₂} {Fun e₁} {v} = sFun λ x → Subst-id


  Subst-id  : {var : typ → Set}{τ₁ τ₂ α β : typ}{μα μβ : trail} →
              {t : term[ var ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
              {v : value[ var ] τ₂} →
                Subst (λ _ → t) v t

  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {Val x} {v} = sVal SubstV-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {App t t₁} {v} = sApp Subst-id Subst-id
  Subst-id {var} {.Nat} {τ₂} {α} {β} {μα} {μβ} {Plus t t₁} {v} = sPlu Subst-id Subst-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {Control x x₁ x₂ e} {v} = sCon (λ k → Subst-id)
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {Prompt x t} {v} = sPro Subst-id

mutual
  eSubstV  : {var : cpstyp → Set} {τ₁ τ : typ} →
             {v₁ : var (cpsT τ) → value[ var ∘ cpsT ] τ₁} →
             {v₁′ : value[ var ∘ cpsT ] τ₁} →
             {v : value[ var ∘ cpsT ] τ} →
             SubstVal v₁ v v₁′ →
             cpsSubstVal (λ y → cpsV {var = var} (v₁ y)) (cpsV v) (cpsV v₁′)
             
  eSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  eSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  eSubstV SubstVal.sNum = cpsSubstVal.sNum
  eSubstV (sFun sub) = sFun (λ x → sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst (sub x) (λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))

  eSubst   : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail} →
             {e₁ : var (cpsT τ) →
               term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {t :  cpsvalue[ var ] cpsM μβ} →
             --{sub : subst-cont′ (λ x → k) (cpsV v) k} →
             --{trail : cpsvalue[ var ] cpsM μα} →
             Subst e₁ v e₂ →
             subst-cont (λ x → k) (cpsV v) k →
             cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
             (cpsTerm e₂ k t)

  eSubst (sVal x) eq = eq (eSubstV x) 
  eSubst (sApp x x₂) eq = ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ → sApp (sApp (sApp (sVal x₁) (sVal x₃)) Subst≠) Subst≠))
  eSubst (sPlu x x₂) eq = ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ → sLet (λ x₄ → Subst≠) (λ x₄ → sPlu (sVal x₁) (sVal x₃))))
  eSubst (sCon x) eq = sLet (λ x₂ → eSubst (x x₂) (λ x₆ → sIdk x₆ SubstV≠)) (λ x₂ → Subst≠)
  eSubst (sPro x) eq = sLet (λ x₂ → Subst≠) λ x₄ → eSubst x (λ x₅ → sIdk x₅ SubstV≠)


  schematicV : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
             
  schematicV {var} {τ₁} {μα = μα} k =
             (v : value[ var ∘ cpsT ] τ₁) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x → k (CPSVar x) t) (cpsV v) (k (cpsV v) t)

  schematic  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
               (k : cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematic  {var} {τ₁} {μα = μα} k =
             (v : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x → k (CPSVar x) t) v (k v t)

  schematicV′ : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
             
  schematicV′ {var} {τ₁} {μα = μα} k =
             (t : cpsvalue[ var ] (cpsM μα)) →
             (v₂ : cpsvalue[ var ] cpsT τ₁) →
             cpsSubst (λ x → k v₂ (CPSVar x)) t (k v₂ t)

  schematicK  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail}{τ : cpstyp} →
               (k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematicK  {var} {τ₁} {μα = μα}{τ = τ} k =
             {v : cpsvalue[ var ] τ} →
             (x : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x₁ → k (CPSVar x₁) x t) v (k v x t)
             --cpsSubst (λ x → k (CPSVar x) t) v (k v t)


  kSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           (k₁ : cpsvalue[ var ] τ →
                  cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
           --{k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           --{t′ : cpsvalue[ var ] (cpsM μα)} →
           --subst-cont k₁ v k₂ →
           schematicK k₁ →
           cpsSubst (λ x → cpsTerm e (k₁ (CPSVar x)) t₁) v (cpsTerm e (k₁ v) t₁)

  kSubst (Val x₁) k₁ {t₁ = t₁} sch = sch (cpsV x₁) t₁
  kSubst (App e e₁) k₁ sch = kSubst e
    (λ x →
       λ v₁ →
         cpsTerm e₁
         (λ v₂ t₂ →
            CPSApp
            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ x (CPSVar v₃) (CPSVar t'')))))))
            (CPSVal t₂)))
    (λ x t →
    kSubst e₁
      (λ x₁ →
         λ v₂ t₂ →
           CPSApp
           (CPSApp (CPSApp (CPSVal x) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal (CPSFun (λ t'' → k₁ x₁ (CPSVar v₃) (CPSVar t'')))))))
           (CPSVal t₂))
      (λ x₁ t₂ → sApp (sApp Subst≠ (sVal (sFun (λ x₂ → sVal (sFun (λ x₃ → sch (CPSVar x₂) (CPSVar x₃)))))))
      Subst≠))
  kSubst (Plus e e₁) k₁ sch = kSubst e
                                (λ x →
                                   λ v₁ →
                                     cpsTerm e₁
                                     (λ v₂ t₂ →
                                        CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                        (λ v₃ → k₁ x (CPSVar v₃) t₂)))
                                (λ x t →
                                kSubst e₁
                                  (λ x₁ →
                                     λ v₂ t₂ →
                                       CPSLet (CPSPlus (CPSVal x) (CPSVal v₂))
                                       (λ v₃ → k₁ x₁ (CPSVar v₃) t₂))
                                  (λ x₁ t₂ → sLet (λ x₂ → sch (CPSVar x₂) t₂)
                                  (λ x₂ → Subst≠)))
  kSubst (Control x₁ x₂ x₃ e) k₁ sch = sLet (λ x → Subst≠) (λ x → sVal (sFun
                                      (λ x₄ → sVal (sFun (λ x₅ → sVal (sFun (λ x₆ → sLet (λ x₇ →
                                      sch (CPSVar x₄) (CPSVar x₇)) (λ x₇ → Subst≠))))))))
  kSubst (Prompt x₁ e) k₁ {t₁ = t₁} sch = sLet (λ x → sch (CPSVar x) t₁) λ x → Subst≠

  tSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] (cpsM μβ)} →
           --(t₁ : var τ → cpsvalue[ var ] (cpsM μβ)) →
           {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
           --(t₂ : cpsvalue[ var ] (cpsM μβ)) →
           --subst-trail {τ₁ = τ₁}{τ₂ = τ₂} t₁ v t₂ →
           schematicV′ k →
           cpsSubst (λ x → cpsTerm e k (CPSVar x)) v (cpsTerm e k v)

  tSubst (Val x) {v = v} sch = sch v (cpsV x)
  tSubst (App e e₁) sch = tSubst e (λ t v₂ → tSubst e₁ (λ t₁ v₃ → sApp Subst≠ (sVal sVar=)))
  tSubst (Plus e e₁) sch = tSubst e (λ t v₂ → tSubst e₁ (λ t₁ v₃ → sLet (λ x → sch t₁ (CPSVar x)) (λ x → Subst≠)))
  tSubst (Control x x₁ x₂ e) sch = sLet (λ x₃ → Subst≠) (λ x₃ → sVal
                                   (sFun (λ x₄ → sVal (sFun (λ x₅ → sVal (sFun (λ x₆ →
                                   sLet (λ x₇ → Subst≠) λ x₇ → sApd (sVal sVar=) Subst≠)))))))
  tSubst (Prompt x e) {v = v} sch = sLet (λ x₁ → sch v (CPSVar x₁)) λ x₁ → Subst≠


  ekSubst  : {var : cpstyp → Set} {τ τ₁ α β : typ} {μα μβ : trail} →
             {e₁ : (var ∘ cpsT) τ → term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsvalue[ var ] (cpsM μβ)} →
             Subst e₁ v e₂ →
             subst-cont k₁ (cpsV v) k₂ →
             cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal x) eq = eq (eSubstV x)
  ekSubst (sApp sub₁ sub₂) eq = ekSubst sub₁ (λ m → ekSubst sub₂ (λ n → sApp (sApp (sApp (sVal m) (sVal n)) (sVal (sFun (λ x → sVal (sFun (λ x₁ → eq SubstV≠)))))) Subst≠))
  ekSubst (sPlu sub₁ sub₂) eq = ekSubst sub₁ (λ m → ekSubst sub₂ (λ n → sLet (λ x → eq SubstV≠) (λ x → sPlu (sVal m) (sVal n))))
  ekSubst (sCon e) eq = sLet (λ x → ekSubst (e x) (λ x₄ → sIdk x₄ SubstV≠)) λ x → sVal (sFun (λ x₄ → sVal (sFun λ x₁ → sVal (sFun (λ x₆ → sLet (λ x₇ → eq SubstV≠) (λ x₇ → Subst≠))))))
  ekSubst (sPro e) eq = sLet (λ v → eq SubstV≠) λ x₁ → ekSubst e (λ x₂ → sIdk x₂ SubstV≠)


-- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  -- ekSubst'  : {var : cpstyp → Set} {τ₁ τ α β : typ} {μα μβ : trail} →
  --             {e₁ : var (cpsT τ) →
  --                   term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
  --             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
  --             {v : value[ var ∘ cpsT ] τ} →
  --             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) →
  --             cpsterm[ var ] (cpsT α)) →
  --             (t : cpsvalue[ var ] (cpsM μβ)) →
  --             Subst e₁ v e₂ →
  --             cpsSubst (λ x → cpsTerm (e₁ x) k t)
  --                     (cpsV v)
  --                     (cpsTerm e₂ k t)

  -- ekSubst' k t (sVal sub) = {!!}
  -- ekSubst' k t (sApp sub₁ sub₂) = {!!}
  -- ekSubst' k t (sPlu x x₁) = {!!}
  -- ekSubst' k t (sCon x) = {!!}
  -- ekSubst' k t (sPro x) = {!!}

  

-- schematic : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
--             (k : cpsvalue[ var ] (cpsT τ₁) →
--                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
--             (t : cpsvalue[ var ] cpsM μα) → Set
-- schematic {var} {τ₁} k  t =
--   (v : cpsvalue[ var ] (cpsT τ₁)) →
--   cpsSubst (λ x → k (CPSVar x) t) v (k v t)

correctCont :  {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail} →
               (e : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
               (k₁ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
               {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
               --{t′ : cpsvalue[ var ] (cpsM μα)} →
               {t₂ : cpsvalue[ var ] (cpsM μβ)} →
               schematic  k₁ →
               --schematicV  k₂ →
               -- ((v : value[ var ∘ cpsT ] τ₁) →
               --  subst-cont k₁ v k₂) →
               ((v : value[ var ∘ cpsT ] τ₁) → (t : cpsvalue[ var ] (cpsM μα)) →
                cpsreduce (k₁ (cpsV v) t) (k₂ (cpsV v) t)) →
               cpsreduce (cpsTerm e k₁ t₂) (cpsTerm e k₂ t₂)

correctCont (Val x₁) k₁ {k₂} {t₂ = t₂} sch₁ x = x x₁ t₂
correctCont (App e e₁) k₁ {k₂}  {t₂} sch₁ x = begin
 (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       t₂)

  ⟶⟨ correctCont e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       {λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃))}
       (λ v t → kSubst e₁
                    (λ x₁ →
                       λ v₂ t₃ →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                          (CPSVal
                           (CPSFun
                            (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                         (CPSVal t₃))
                    (λ x₁ t₁ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠) )
                    (λ v t → correctCont e₁
                                 (λ v₂ t₃ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                                    (CPSVal t₃))
                                 {λ v₂ t₃ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₁ → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v₁) (CPSVar t'')))))))
                                    (CPSVal t₃)}
                                 (λ v₁ t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
                                 (λ v₁ t₁ → rApp₁ (rApp₂ (rFun (λ x₁ → rFun (λ x₂ → x (Var x₁) (CPSVar x₂)))))))  ⟩

  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       t₂)

  ∎
correctCont (Plus e e₁) k₁ {k₂} {t₂ = t₂} sch₁ x = begin
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       t₂)
  ⟶⟨ correctCont e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       {λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₃))}
       (λ v t → kSubst e₁
                    (λ x₁ →
                       λ v₂ t₃ →
                         CPSLet (CPSPlus (CPSVal x₁) (CPSVal v₂))
                         (λ v₁ → k₁ (CPSVar v₁) t₃))
                    (λ x₁ t₁ → sLet (λ x₂ → Subst≠) (λ x₂ → sPlu
                    (sVal sVar=) Subst≠)))
       (λ v t → correctCont e₁
                    (λ v₂ t₃ →
                       CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                       (λ v₁ → k₁ (CPSVar v₁) t₃))
                    {λ v₂ t₃ →
                       CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                       (λ v₁ → k₂ (CPSVar v₁) t₃)}
                    (λ v₁ t₁ → sLet (λ x₁ → Subst≠)
                    (λ x₁ → sPlu Subst≠ (sVal sVar=)))
                    (λ v₁ t₁ → rLet₂ (λ x₁ → x (Var x₁) t₁))) ⟩
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₃)))
       t₂)
  ∎
correctCont (Control x₁ x₂ x₃ e) k₁ {k₂} {t₂ = t₂} sch₁ x = begin
  (cpsTerm (Control x₁ x₂ x₃ e) k₁ t₂)
  ⟶⟨ rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → x (Var x₄) (CPSVar x₇)))))) ⟩
  (cpsTerm (Control x₁ x₂ x₃ e) k₂ t₂)
  ∎

correctCont (Prompt x₁ e) k₁ {k₂} {t₂ = t₂} sch₁ x = rLet₂ (λ x₂ → x (Var x₂) t₂)





correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] (cpsM μβ)) →
             --{sch :  schematicV k} →
             --{sch' : schematicV′ k} →
             --{t′ : cpsvalue[ var ] (cpsM μα)} →
             schematicV k →
             schematicV′ k →
             Reduce e e′ →
             cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)   --⟦ e ⟧k = ⟦ e′ ⟧k

correctEta {e′ = e′} k t sch sch'  (RBeta {e₁ = e₁} {v₂ = v₂} x) = begin
  cpsTerm (App (Val (Fun e₁)) (Val v₂)) k t
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst  x λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))) ⟩
  CPSApp
    (CPSApp
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              cpsTerm e′
              (λ v t''' →
                 CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v)) (CPSVal t'''))
              (CPSVar z₁))))))
     (CPSVal
      (CPSFun
       (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
    (CPSVal t)
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → kSubst e′
                                          (λ y →
                                             λ v t''' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t'''))
                                          (λ x₂ t₁ → sApp (sApp (sVal sVar=) Subst≠)
                                          Subst≠))))) ⟩
  CPSApp
    (CPSVal
     (CPSFun
      (λ z →
         cpsTerm e′
         (λ z₁ z₂ →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
             (CPSVal z₁))
            (CPSVal z₂))
         (CPSVar z))))
    (CPSVal t)
  ⟶⟨ rBeta (tSubst e′ λ t₁ v₃ → sApp Subst≠ (sVal sVar=)) ⟩
  cpsTerm e′
    (λ z₁ z₂ →
       CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
        (CPSVal z₁))
       (CPSVal z₂))
    t
    ⟶⟨ correctCont e′
         (λ z₁ z₂ →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
             (CPSVal z₁))
            (CPSVal z₂))
            {k}
         (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v t₁ → (begin
           (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t''))))))
        (CPSVal (cpsV v)))
       (CPSVal t₁))
        ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sch v (CPSVar x₁))))) ⟩
        CPSApp (CPSVal (CPSFun (λ z → k (cpsV v) (CPSVar z)))) (CPSVal t₁)
        ⟶⟨ rBeta (sch' t₁ (cpsV v)) ⟩
        (k (cpsV v) t₁)
        ∎)) ⟩
  cpsTerm e′ k t
  ∎


  
correctEta k t sch sch' (RPlus {τ₂} {μα} {n₁} {n₂}) = begin
  (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂))) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
  CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet (sch (Num (n₁ + n₂)) t) ⟩
  k (CPSNum (n₁ + n₂)) t
  ∎
 
correctEta k t sch sch' (RFrame  (App₁ e₃) x) = correctEta (λ v₁ →
                                                      cpsTerm e₃
                                                      (λ v₂ t₂ →
                                                         CPSApp
                                                         (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                                          (CPSVal
                                                           (CPSFun
                                                            (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                         (CPSVal t₂))) t (λ v t₁ →
                                                         kSubst e₃
                                                           (λ x₁ →
                                                              λ v₂ t₂ →
                                                                CPSApp
                                                                (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                                                                 (CPSVal
                                                                  (CPSFun
                                                                   (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t'')))))))
                                                                (CPSVal t₂))
                                                           (λ x₁ t₂ → sApp (sApp (sApp (sVal sVar=) Subst≠)
                                                           Subst≠) Subst≠)) (λ t₁ v₂ → tSubst e₃ λ t₂ v₃ →
                                                           sApp (sApp Subst≠ Subst≠) (sVal sVar=)) x
                                                           
correctEta k t sch sch' (RFrame (App₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                     (CPSVal t₂)) t
                                                     (λ v t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=))
                                                     Subst≠) Subst≠)
                                                     (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))  x
                                                     
correctEta k t sch sch'  (RFrame (Plus₁ e₃) x) = correctEta (λ v₁ →  cpsTerm e₃
                                                                          (λ v₂ t₂ →
                                                                             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                                                             (λ v → k (CPSVar v) t₂))) t
                                                                             (λ v t₁ →
                                                                             kSubst e₃
                                                                               (λ x₁ →
                                                                                  λ v₂ t₂ →
                                                                                    CPSLet (CPSPlus (CPSVal x₁) (CPSVal v₂)) (λ v₁ → k (CPSVar v₁) t₂))
                                                                               (λ x₁ t₂ → sLet (λ x₂ → Subst≠)
                                                                               (λ x₂ → sPlu (sVal sVar=) Subst≠)) )
                                                                                (λ t₁ v₂ → tSubst e₃ λ t₂ v₃ →
                                                                                sLet (λ x₁ → sch' t₂ (CPSVar x₁)) (λ x₁ → Subst≠))  x
                                                  
correctEta k t sch sch'  (RFrame (Plus₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (λ v → k (CPSVar v) t₂)) t (λ v t₁ → sLet (λ x₁ → Subst≠)
                                                      (λ x₁ → sPlu Subst≠ (sVal sVar=)))
                                                      (λ t₁ v₂ → sLet (λ x₁ → sch' t₁ (CPSVar x₁))
                                                      λ x₁ → Subst≠)  x
                                                      
correctEta k t sch sch' (RFrame {e₁ = e₁} {e₂ = e₂} (Pro x₁) x) = begin
  (CPSLet (cpsTerm e₁ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ (correctEta (CPSIdk x₁) (CPSId) (λ v t₁ → sIdk sVar= SubstV≠) (λ t₁ v₂ → sIdk SubstV≠ sVar=) x) ⟩
  (CPSLet (cpsTerm e₂ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ∎
  
correctEta k t sch sch' (RPrompt {v₁ = v₁}) = begin
  (CPSLet (CPSIdk refl (cpsV v₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
  CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟶⟨ rLetApp ⟩
  CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta (sch v₁ t) ⟩
  (k (cpsV v₁) t)
  ∎
correctEta k t sch sch' (RControl p₁ p₂ x₁ x₂ x₃ x e) = {!!}

