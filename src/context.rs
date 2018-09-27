use std::mem;
use std::ops::Add;
use frunk::{Generic, LabelledGeneric};
use frunk::hlist::{HCons, HList, HNil, LiftFrom, Selector};
use frunk::indices::{Here, There};
// use frunk::prelude::*;


pub trait AtIndex<Index>/* : Selector<Self::Output, Index>*/
{
    type Output;
}

impl<Head, Tail> AtIndex<Here> for HCons<Head, Tail>
{
    type Output = Head;
    // fn select(&self) -> Selector<Output, Tail>
    // type Selector : Selector<, >;
}

impl<Head, Tail, TailIndex> AtIndex<There<TailIndex>> for HCons<Head, Tail>
    where Tail : AtIndex<TailIndex>
{
    type Output = Tail::Output;
}

/// Note: Here represents 0 and There K represents K.
pub trait PeanoLen {
    type PeanoLen;
}

impl PeanoLen for HNil {
    type PeanoLen = Here;
}

impl<Head, Tail> PeanoLen for HCons<Head, Tail>
    where Tail : PeanoLen,
{
    type PeanoLen = There<Tail::PeanoLen>;
}

    //Selector<FromTail, There<TailIndex>> for HCons<Head, Tail> 

/* #[derive(Generic, LabelledGeneric)]
pub struct Context<Subs : HList> {
    subs: Subs,
} */

pub trait RawContext {
    type Subs : HList;
}

impl<T : HList> RawContext for T {
    type Subs = Self;
}

pub trait Context : RawContext {
}/*+ Sized where Self::Subs : Generic<Repr = Self> /* where Self : Generic<Repr = Self::Subs>*/ {
}*/

impl</*Subs, */T : RawContext> Context for T /*where T : Generic<Repr = Subs> */{
}

/* Context: IAdd<HList> where <Self as IAdd<HList>>::Output

impl IAdd<HList> for C */

/* impl LiftFrom<Subs, > */

/* pub trait ContextSubs<Subs : HList> {
    type Output : Context + LiftFrom<>;
} */

/* impl<Prefix, Suffix> LiftFrom<Prefix, Suffixed<Suffix>> for <Prefix as Add<Suffix>>::Output where
    Prefix: HList + Add<Suffix>,
    Suffix: Default, */

/// RDecl is (canonically) either Def or Assum
pub trait RDecl//<Ctx : Context, Index>
    //where Ctx::Subs : AtIndex<Index>,
{
    type Type;// : JudgeOfSort<>;
}

// #[derive(Generic, LabelledGeneric)]
pub struct Assum<Type> {
    ty: Type,
}

// #[derive(Generic, LabelledGeneric)]
pub struct Decl<Body, Type> {
    bd: Body,
    ty: Type,
}

impl<Type> RDecl for Assum<Type> {
    type Type = Type;
}

impl<Body, Type> RDecl for Decl<Body, Type> {
    type Type = Type;
}

// #[derive(Generic)]
pub struct Set;

// #[derive(Generic)]
pub struct Type;

pub struct App<Fun, /*Args : HList*/Arg> {
    fun: Fun,
    // args: Args,
    arg: Arg,
}

pub struct Lambda<Type, Body> {
    ty: Type,
    bd: Body,
}

pub struct Prod<Domain, CoDomain> {
    domain: Domain,
    codomain: CoDomain,
}

// #[derive(Generic, LabelledGeneric)]
pub struct Sort<S> {
    sort: S,
}

// #[derive(Generic, LabelledGeneric)]
pub struct Rel<Index> {
    index: Index,
}

pub trait IAdd<RHS> {
    type Output;
}

impl<M> IAdd<Here> for Rel<M> {
    type Output = There<M>;

    /* fn add(self, rhs: Here) -> Self::Output {
        self
    } */
}

impl<M, N> IAdd<There<N>> for Rel<M>
    where Rel<M> : IAdd<N>
{
    type Output = There<<Rel<M> as IAdd<N>>::Output>;

    /* fn add(self, rhs: There<M>) -> There<<Rel<M> as Add<N>>::Output>
        //Self::Output
    {
        // NOTE: Shouldn't really require unsafe (should be able to
        // construct it Peano-style as { There : rhs.there.add() }...
        // but we don't have access to the module.
        unsafe { mem::transmute(self) }
    } */
}

/// NOTE: For ISub purposes, Here means 0, not 1!
pub trait ISub<RHS> {
    type Output;
}

impl<M> ISub<Here> for Rel<M> {
    type Output = M;
}

impl<N> ISub<There<N>> for Rel<Here> {
    type Output = Here;
}

impl<M, N> ISub<There<N>> for Rel<There<M>>
    where Rel<M> : ISub<N>
{
    type Output = <Rel<M> as ISub<N>>::Output;
}

/// Trait used for dealing with lifts.
/// NOTE: Lift (K = There<K'>, IndexDiffK = Self - K')
pub trait RelocRel<N, IndexDiffK> {
    type Output;
}

/// NOTE: Treat K as 1 + K', where K' is what we actually care about.
///       
/// NOTE: Here = ((1 + Index) - K)
///
/// NOTE: If Here, Index ≤ K', so we return Index unchanged.
impl<N, Index> RelocRel<N, Here> for Rel<Index> {
    type Output = Index;
}

/// NOTE: Treat K as 1 + K', where K' is what we actually care about.
///
/// NOTE: There<IndexDiffK> = ((1 + Index) - K)
///
/// NOTE: If There<IndexDiffK>, K' < Index, so we shift Index by N.
impl<N, IndexDiffK, Index> RelocRel<N, There<IndexDiffK>> for Rel<Index>
    where Self : IAdd<N>,
{
    type Output = <Self as IAdd<N>>::Output;
}


/// K = Lifts, N = Shifts.  Lifts are evaluated first.
pub trait LiftN<K, N> {
    type Output;
}

impl<K, N, T, C> LiftN<K, N> for Prod<T, C>
    where
        T: LiftN<K, N>,
        C: LiftN<There<K>, N>,
{
    type Output = Prod<<T as LiftN<K, N>>::Output, <C as LiftN<There<K>, N>>::Output>;
}

impl<K, N, T, B> LiftN<K, N> for Lambda<T, B>
    where
        T: LiftN<K, N>,
        B: LiftN<There<K>, N>,
{
    type Output = Prod<<T as LiftN<K, N>>::Output, <B as LiftN<There<K>, N>>::Output>;
}

impl<K, N, F, A> LiftN<K, N> for App<F, A>
    where
        F: LiftN<K, N>,
        A: LiftN<K, N>,
{
    type Output = App<<F as LiftN<K, N>>::Output, <A as LiftN<K, N>>::Output>;
}

impl<K, N, S> LiftN<K, N> for Sort<S> {
    type Output = Self;
}

/// Lifting

impl<K, N, Index> LiftN<K, N> for Rel<Index>
    where
        // NOTE: K is "really" There<K'>, where K' is what we care about.
        Rel<There<Index>> : ISub<K>,
        // Compute the necessary relocation.
        Self: RelocRel<N, <Rel<There<Index>> as ISub<K>>::Output>,
{
    type Output = Rel<<Self as RelocRel<N, <Rel<There<Index>> as ISub<K>>::Output>>::Output>;
}

pub trait Lift<Index> : LiftN<Here, Index>
{
    type Output;
}

impl<T, Index> Lift<Index> for T where T : LiftN<Here, Index>
{
    type Output = <T as LiftN<Here, Index>>::Output;
}

/// Lamv = Subs, N = Shifts.  Subs are evaluated first.
///
/// Reminder : N = Here means None, and N = Theirs<N'> gives the actual N' we want.
pub trait SubstRec<N, LamV, LV> {
    type Output;
}

impl<N, LamV, LV, T, C> SubstRec<N, LamV, LV> for Prod<T, C>
    where
        T: SubstRec<N, LamV, LV>,
        C: SubstRec<There<N>, LamV, LV>,
{
    type Output = Prod<<T as SubstRec<N, LamV, LV>>::Output, <C as SubstRec<There<N>, LamV, LV>>::Output>;
}

impl<N, LamV, LV, T, B> SubstRec<N, LamV, LV> for Lambda<T, B>
    where
        T: SubstRec<N, LamV, LV>,
        B: SubstRec<There<N>, LamV, LV>,
{
    type Output = Prod<<T as SubstRec<N, LamV, LV>>::Output, <B as SubstRec<There<N>, LamV, LV>>::Output>;
}

impl<N, LamV, LV, F, A> SubstRec<N, LamV, LV> for App<F, A>
    where
        F: SubstRec<N, LamV, LV>,
        A: SubstRec<N, LamV, LV>,
{
    type Output = App<<F as SubstRec<N, LamV, LV>>::Output, <A as SubstRec<N, LamV, LV>>::Output>;
}

impl<N, LamV, LV, S> SubstRec<N, LamV, LV> for Sort<S> {
    type Output = Self;
}

/// Substitutions

/// Trait used for dealing with inbounds substitutions.
///
/// NOTE: We secretly know that LV = LamV::PeanoLen, and therefore
///       LV = Theirs<LV'> at all times.
///
/// NOTE: IndexDiffK = K - Depth (for real; it is positive).
///
/// NOTE: LVDiff = (IndexDiffK + 1) - LV (+ 1, so Here represents 0)
///
/// LDiff = Here → (K - Depth + Here) - (LV' + Here) ≤ Here, i.e. K - Depth ≤ LV'.
///
/// As a result, in the Here case we can assume K - Depth is in bounds and therefore
/// AtIndex should always succeed for IndexDiffK.
///
/// (We may not actually need to know LV positive for this to work, but it's convincing).
/*/// NOTE: We secretly know that LV = LamV::PeanoLen, and therefore
///       LV = Theirs<LV'> at all times.  This allows us to know
///       that if LDiff = Here (i.e. (K - Depth) - LV ≤ 0, i.e.
///       K - Depth ≤ LV), then K - Depth is 
///       then */
pub trait SubstRel2<N, LamV, LV, IndexDiffK, LVDiff> {
    type Output; 
}

/// Here case : InDiffK is in-bounds and N = Here.
///
/// Important reminder: if N = Here, don't lift!
impl<LamV, LV, IndexDiffK, Index> SubstRel2<Here, LamV, LV, IndexDiffK, Here> for Rel<Index>
    where
        LamV : AtIndex<IndexDiffK>,
{
    type Output =<LamV as AtIndex<IndexDiffK>>::Output;
}

/// Here case : InDiffK is in-bounds and N = There N'.
///
/// Important reminder: if N = Here, don't lift!
impl<N, LamV, LV, IndexDiffK, Index> SubstRel2<There<N>, LamV, LV, IndexDiffK, Here> for Rel<Index>
    where
        LamV : AtIndex<IndexDiffK>,
        <LamV as AtIndex<IndexDiffK>>::Output : Lift<N>,
{
    type Output = <<LamV as AtIndex<IndexDiffK>>::Output as Lift<N>>::Output;
}

/// There case : LDiff = There<LDiff'>.
/// Then Here < (K - Depth + Here) - (LV' + Here), i.e.
/// Here < (K - Depth) - LV', which implies Here < K - LV'.  Fortunately this implies that
/// K > Here + LV' = LV; so we can replicate the effect of stripping off the There<_> from the
/// output of K - LV' (to get the real answer) by instead stripping it off of K up front.  The
/// subtraction is still in bounds, it just becomes Here ≤ K' - LV'; and again, we should be
/// exhaustive here for all indices (there should be no missed cases).
impl<N, LamV, LV, IndexDiffK, LVDiff, Index> SubstRel2<N, LamV, LV, IndexDiffK, There<LVDiff>> for Rel<There<Index>>
    where
        Rel<Index> : ISub<LV>,
{
    type Output = Rel<<Rel<Index> as ISub<LV>>::Output>;
}

/// LV' < K - Depth, i.e. There<LV'> ≤ K - Depth, so
/// Depth ≤ K - There<Lv'>.
///
/// Trait used for dealing with substitutions.
///
/// NOTE: Lift (K = There<K'>, IndexDiffK = Self - K')
pub trait SubstRel<N, LamV, LV, IndexDiffK> {
    type Output;
}

/// NOTE: Treat N as 1 + K', where K' is what we actually care about.
///       
/// NOTE: Here = ((1 + Index) - N)
///
/// NOTE: If Here, Index ≤ K', so we return Index unchanged.
impl<N, LamV, LV, Index> SubstRel<N, LamV, LV, Here> for Rel<Index> {
    type Output = Rel<Index>;
}

/// NOTE: Treat N as 1 + K', where K' is what we actually care about.
///
/// NOTE: There<IndexDiffK> = ((1 + Index) - N)
///
/// NOTE: If There<IndexDiffK>, K' < Index, so we split further.
impl<N, LamV, LV, IndexDiffK, Index> SubstRel<N, LamV, LV, There<IndexDiffK>> for Rel<Index>
    where
        // Recall : PeanoLen is actually len + 1, so this all works out
        // (output is 1+ as well).  This is lv - (k - depth), i.e. (k - depth) ≤ lv.
        Rel<There<IndexDiffK>> : ISub<LV>,
        // Note that if lv < k - depth, depth < k - lv, so k - lv > 0; therefore,
        // since subtraction normally returns output + 1, and we know the output is
        // positive, we can get the real output by subtracting 1 from k first (it
        // won't mess up at 0 because (k - 1) - lv ≥ 0).
        // Even though it's not always necessary, we also compute k - lv here to
        // be able to extract the There pattern (if k - depth ≤ lv
        Rel<Index> : SubstRel2<N, LamV, LV, IndexDiffK, <Rel<There<IndexDiffK>> as ISub<LV>>::Output>,
        /*  else if k-depth <= lv then lift_substituend depth lamv.(k-depth-1)

         */
        // Self : IAdd<N>,
{
    type Output = <Self as SubstRel2<N, LamV, LV, IndexDiffK, <Rel<There<IndexDiffK>> as ISub<LV>>::Output>>::Output;
}

impl<N, LamV, LV, Index> SubstRec<N, LamV, LV> for Rel<Index>
    where
        // NOTE: N is "really" There<N'>, where N' is what we care about.
        Rel<There<Index>> : ISub<N>,
        // Compute the necessary relocation.
        Self: SubstRel<N, LamV, LV, <Rel<There<Index>> as ISub<N>>::Output>,
{
    type Output = <Self as SubstRel<N, LamV, LV, <Rel<There<Index>> as ISub<N>>::Output>>::Output;
}
/*
    fn substrec<T>(&self,
                   &(depth, ref lamv): &(Option<Idx>, &[Substituend<T>])) -> IdxResult<Constr>
        where
            T: Borrow<Constr>,
    {
        match *self {
            Constr::Rel(k_) => {
                // FIXME: For below, ensure u32 to usize is always a valid cast.
                let d = depth.map(u32::from).unwrap_or(0) as usize;
                // NOTE: This can only fail if we compile with addresses under 64 bits.
                let k = usize::try_from(k_)?;
                // After the above, we know k is a valid non-negative i64.
                if k <= d {
                    Ok(self.clone())
                } else if let Some(sub) = lamv.get(k - d - 1) {
                    // Note that k - d above is valid (and > 0) because 0 ≤ d < k;
                    // therefore, 0 ≤ k - depth - 1, so that is valid.
                    // Also, the unwrap() below is granted because 0 < k.
                    // FIXME: There is a better way of dealing with this.
                    sub.borrow().lift(depth.unwrap())
                } else {
                    // k - lamv.len() is valid (and > 0) because if lamv.get(k - d - 1) = None,
                    // lamv.len() ≤ k - d - 1 < k - d ≤ k (i.e. lamv.len() < k), so
                    // 0 < k - lamv.len() (k - lamv.len() is positive).
                    // Additionally, since we know 0 < lamv.len() < k, and k is a valid positive
                    // i64, lamv.len() is also a valid positive i64.
                    // So the cast is valid.
                    Ok(Constr::Rel(k_ - lamv.len() as i64))
                }
            },
            _ => self.map_constr_with_binders(
                |&mut (ref mut depth, _)| {
                    *depth = match *depth {
                        None => Some(Idx::ONE),
                        Some(depth) => Some(depth.checked_add(Idx::ONE)?),
                    };
                    Ok(())
                },
                Self::substrec,
                &(depth, lamv)
            )
        }
    }
*/

/*
    /// (subst1 M c) substitutes M for Rel(1) in c
    /// we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
    /// M1,...,Mn for respectively Rel(1),...,Rel(n) in c
    pub fn substn_many<T>(&self, lamv: &[Substituend<T>], n: Option<Idx>) -> IdxResult<Constr>
        where
            T: Borrow<Constr>,
    {
        let lv = lamv.len();
        if lv == 0 { return Ok(self.clone()) }
        else { self.substrec(&(n, lamv)) }
    }
*/
/// Reminder : N = Here means None, and N = Theirs<N'> gives the actual N' we want.
pub trait SubstNMany<LamV : HList, N> {
    type Output;
}

impl<N, C> SubstNMany<HNil, N> for C
{
    type Output = C;
}

/// FIXME: Pass around PeanoLen-1 (which is actually the proper length).
impl<Lam, LamV : HList, N, C> SubstNMany<HCons<Lam, LamV>, N> for C
    where
        LamV : PeanoLen,
        C : SubstRec<N, HCons<Lam, LamV>, <HCons<Lam, LamV> as PeanoLen>::PeanoLen>,
{
    type Output = <C as SubstRec<N, HCons<Lam, LamV>, <HCons<Lam, LamV> as PeanoLen>::PeanoLen>>::Output;
}

/*
    pub fn substnl<T, C>(&self, laml: C, n: Option<Idx>) -> IdxResult<Constr>
        where
            C: IntoIterator<Item=T>,
            T: Borrow<Constr>,
    {
        let lamv: Vec<_> = laml.into_iter().map( |i| Substituend::make(i) ).collect();
        self.substn_many(&lamv, n)
    }

    pub fn substl<T, C>(&self, laml: C) -> IdxResult<Constr>
        where
            C: IntoIterator<Item=T>,
            T: Borrow<Constr>,
    {
        self.substnl(laml, None)
    }
*/

pub trait Subst1<Lam> {
    type Output;
}

/// Reminder : N = Here means None, and N = Theirs<N'> gives the actual N' we want.
impl<Lam, C> Subst1<Lam> for C
    where
        C : SubstNMany<Hlist![Lam], Here>,
{
    type Output = <C as SubstNMany::<Hlist![Lam], Here>>::Output;
}
/*
    pub fn subst1(&self, lam: &Constr) -> IdxResult<Constr> {
        let lamv = [Substituend::make(lam)];
        self.substn_many(&lamv, None)
    }
*/

pub trait WhdAll<Ctx> where Ctx : Context {
    type Output;
}

/// Temporary WhdAll implementation until real reduction is implemented.
impl<Term, Ctx : Context> WhdAll<Ctx> for Term {
    type Output = Term;
}

pub struct PbConv;

pub struct PbCumul;

pub trait FConv<CvPb, T1, T2> : Context {
}

/// Temporary conversion hack: exact equality.
impl<CvPb, /*T1, T2*/T, Ctx> FConv<CvPb, /*T1*/T, /*T2*/T> for Ctx
    where
        // T1 : Execute<Ctx, Type = Self>,
        // T2 : Execute<Ctx, Type = Self>,
        Ctx : Context,
{
}

/// Self is the type context.
pub trait ConvLeq<T1, T2> : Context /*: JudgeOfSort*/ {
}

impl<T1, T2, Ctx> ConvLeq<T1, T2> for Ctx
    where
        // T1 : Execute<Ctx, Type = Self>,
        // T2 : Execute<Ctx, Type = Self>,
        Ctx : Context,
        Ctx : FConv<PbCumul, T1, T2>,
{
}

pub trait JudgeOfSort {
    // type Sort;
}

/* impl<S> JudgeOfSort for Sort<S> {
    type Sort = S;
} */
impl JudgeOfSort for Set {}

impl JudgeOfSort for Type {}

pub trait TypeJudgment<Ctx> where Ctx : Context {
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<S, Ctx : Context> TypeJudgment<Ctx> for Sort<S>
    where S : JudgeOfSort,
{
    type Sort = S;

    /* ty.whd_all(self, iter::empty())?; // Mutates in-place.
    match *ty {
        Constr::Sort(ref s) => Ok((self, s)),
        _ => Err(Box::new(CaseError::Type(error_not_type(self, (c.clone(), ty_.clone()))))),
    } */
}

pub trait JudgeOfType<Ctx> where Ctx : Context {
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<Ctx : Context> JudgeOfType<Ctx> for Sort<Set> {
    type Sort = Type;
}

pub trait JudgeOfApply<H, HJ, Ctx> where Ctx : Context {
    type Type;
}

impl<Ctx, H, HJ, T, C> JudgeOfApply<H, HJ, Ctx> for Prod<T, C>
    where
        Ctx : Context,
        Ctx : ConvLeq<HJ, T>,
        C : Subst1<H>,
/*

            match typ {
                Constr::Prod(o) => {
                    let (_, ref c1, ref c2) = *o;
                    if let Err(e) = self.conv_leq(hj, c1, iter::empty()) {
                        return Err(CaseError::from_conv(e, move ||
                            // NOTE: n + 1 is always in-bounds for usize because argjv.len() must
                            // be isize::MAX or smaller (provided pointers are at least 1 byte and
                            // argjv is backed by a vector, which is the case here).
                            error_cant_apply_bad_type(
                                self, (n + 1, (*c1).clone(), hj.clone()),
                                (f.clone(), funj.clone()),
                                argjv.map( |&(h, ref hj)| (h.clone(), hj.clone()))
                                     .collect())))
                    }
                    typ = c2.subst1(h)?;
                },
                _ => return Err(Box::new(CaseError::Type(
                        error_cant_apply_not_functional(
                            self, (f.clone(), funj.clone()),
                            argjv.map( |&(h, ref hj)| (h.clone(), hj.clone())).collect())))
                    ),
            }
 */
{
    type Type = C::Output;
}

pub trait SortOfProduct<T, C> : Context
    where
        /*Sort<T>*/T : JudgeOfSort,
        /*Sort<C>*/C : JudgeOfSort,
{
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<Ctx : Context> SortOfProduct<Type, Type> for Ctx {
    type Sort = Type;
}

impl<Ctx : Context> SortOfProduct<Type, Set> for Ctx {
    type Sort = Type;
}

impl<Ctx : Context> SortOfProduct<Set, Type> for Ctx {
    type Sort = Type;
}

impl<Ctx : Context> SortOfProduct<Set, Set> for Ctx {
    type Sort = Set;
}
/*
    fn sort_of_product<'a>(&self, domsort: &Sort, rangsort: &'a Sort) -> IdxResult<Cow<'a, Sort>> {
        Ok(match (domsort, rangsort) {
            // Product rule (s, Prop, Prop)
            (_, &Sort::Prop(SortContents::Null)) => Cow::Borrowed(rangsort),
            // Product rule (Prop/Set,Set,Set)
            (&Sort::Prop(_), &Sort::Prop(SortContents::Pos)) => Cow::Borrowed(rangsort),
            // Product rule (Type,Set,?)
            (&Sort::Type(ref u1), &Sort::Prop(SortContents::Pos)) =>
                if let Engagement::ImpredicativeSet = *self.stratification.engagement() {
                    // Rule is (Type,Set,Set) in the Set-impredicative calculus
                    Cow::Borrowed(rangsort)
                } else {
                    // Rule is (Type_i,Set,Type_i) in the Set-predicative calculus
                    // FIXME: Because we mutate the first argument in-place, we swap the argument
                    // order here compared to the OCaml implementation.  Hopefully, this doesn't
                    // affect the result of sup in any significant way (it *shouldn't*, I think),
                    // but we need to double check this.
                    let mut u0 = Univ::type0(&self.globals.univ_hcons_tbl);
                    u0.sup(u1, &self.globals.univ_hcons_tbl)?;
                    Cow::Owned(Sort::Type(u0))
                },
            // Product rule (Set,Type_i,Type_i)
            (&Sort::Prop(SortContents::Pos), &Sort::Type(ref u2)) => {
                let mut u0 = Univ::type0(&self.globals.univ_hcons_tbl);
                u0.sup(u2, &self.globals.univ_hcons_tbl)?;
                Cow::Owned(Sort::Type(u0))
            },
            // Product rule (Prop,Type_i,Type_i)
            (&Sort::Prop(SortContents::Null), &Sort::Type(_)) => Cow::Borrowed(rangsort),
            // Product rule (Type_i,Type_i,Type_i)
            (&Sort::Type(ref u1), &Sort::Type(ref u2)) => {
                // NOTE: The way sup (really merge_univs) is currently written, this clone is
                // somewhat extraneous...
                // TODO: see if merge_univs can be fixed to exploit mutability of one of its
                // arguments.
                let mut u1 = u1.clone();
                u1.sup(u2, &self.globals.univ_hcons_tbl)?;
                Cow::Owned(Sort::Type(u1))
            },
        })
 * 
*/

/* pub trait DecomposeApp<F, Args : HList> : Context
{
    type F;
    type Args : HList;
}

/// Note: list is reversed!
impl<F, A, Args : HList, Ctx : Context> DecomposeApp<App<F, A>, Args> for Ctx
    where Ctx : DecomposeApp<F, HCons<A, Args>>
{
    type Args = <Ctx as DecomposeApp<F, HCons<A, Args>>>::Args;
}

impl<Index, A, Args : HList, Ctx : Context> DecomposeApp<Rel<Index>, Args> for Ctx
{
    type Args = <Ctx as DecomposeApp<F, HCons<A, Args>>>::Args;
} */

pub trait Execute<Ctx> where Ctx : Context {
    type Type : /*JudgeOfSort + *//*?Sized*/;// : JudgeOfSort<Ctx> + ?Sized;
}

impl<S, Ctx> Execute<Ctx> for Sort<S>
    where
        Ctx : Context,
        Self : JudgeOfType<Ctx>,
        // Ctx : Execute<Ty::Unlift, Output=Set>,
        // Ctx::Subs : AtIndex</*::Unlifted*/Index>,
        // <Ctx::Subs as AtIndex<Index>>::Output: RDecl,
        // <<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type : Lift<Index>,
        // <<<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type as Lift<Index>>::Output : JudgeOfSort<Ctx>
        // Ty : UnLift<Index>,
{
    type Type = Sort<<Self as JudgeOfType<Ctx>>::Sort>;
}

impl<Index, Ctx> Execute<Ctx> for Rel<Index>
    where
        Ctx : Context,
        // Ctx : Execute<Ty::Unlift, Output=Set>,
        Ctx::Subs : AtIndex</*::Unlifted*/Index>,
        <Ctx::Subs as AtIndex<Index>>::Output: RDecl,
        <<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type : Lift<Index>,
        // <<<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type as Lift<Index>>::Output : JudgeOfSort/*<Ctx>*/
{
    type Type = <<<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type as Lift<Index>>::Output;
}

impl<F, A, Ctx> Execute<Ctx> for App<F, A>
    where
        Ctx: Context,
        // Ctx : DecomposeApp<F, HCons<A, HNil>>,
        A: Execute<Ctx>,
        F: Execute<Ctx>,
        F::Type : WhdAll<Ctx>,
        <F::Type as WhdAll<Ctx>>::Output : JudgeOfApply<A, A::Type, Ctx>,
        // <Term::Type as WhdAll<Ctx>>::Output : TypeJudgment<Ctx>,
        // <F as Execute<Ctx>>::Type : WhdAll<Ctx>,
/*
    fn judge_of_apply<'a, 'e, I>(&'e mut self, f: &Constr, funj: &Constr, argjv: I
                                ) -> CaseResult<'e, 'b, 'g, (&'e mut Self, Constr)>
        where
            I: Clone + Iterator<Item=&'a (&'a Constr, Constr)>,
    {
        let mut typ = funj.clone(); // We remember the old funj for error reporting purposes.
        for (n, &(h, ref hj)) in argjv.clone().enumerate() {
            typ.whd_all(self, iter::empty())?; // Mutates in-place
            ...
        }
        return Ok((self, typ))
    }
*/
{
    type Type = <<F::Type as WhdAll<Ctx>>::Output as JudgeOfApply<A, A::Type, Ctx>>::Type;
/*
                let mut o = o;
                // Initialize with the arguments we know we need for sure.
                // TODO: It's possible we could avoid allocating a Vec for args *or* jl with a
                // custom iterator... as it is, we end up taking up space anyway since we remember
                // args in order to ease error reporting (though it would not be hard to fix just
                // that problem).
                let mut jl = Vec::new();
                let mut env = self;
                loop {
                    let (ref f, ref args) = **o;
                    // Take advantage of knowledge of the length to add capacity more quickly
                    // than we otherwise might.
                    jl.reserve(args.len());
                    // We process the arguments in reverse order.  This allows us to avoid
                    // allocating an intermediate vector to store appended arguments if it turns
                    // out that f is itself an application.  In theory, this should be perfectly
                    // fine, since for this part of the check all the terms in the application can
                    // be checked in parallel.  In practice, since this evaluates in a different
                    // order from the current Coq implementation, it won't always error in the same
                    // way, which might be annoying for fuzzing purposes, but since this is the
                    // checker it shouldn't normally matter for end users.
                    for arg in args.iter().rev() {
                        let env_ = env;
                        let (env_, j) = env_.execute(arg)?;
                        env = env_;
                        jl.push((arg, j));
                    }
                    // If f is an App, continue to evaluate the arguments of the application in f.
                    if let Constr::App(ref o_) = *f { o = o_ } else { break }
                }
                // Now we've evaluated all the arguments to some non-application Constr (note that
                // jl is reversed, hence the re-reversals below!) so it's time to type f.
                let f = &(**o).0;
                let j = match *f {
                    Constr::Ind(ref o) => // Sort-polymorphism of inductive types
                        env.judge_of_inductive_knowing_parameters(o, jl.iter()
                                                                       .map(|j| &j.1).rev())?,
                    Constr::Const(ref o) => { // Sort-polymorphism of constant
                        let env_ = env;
                        let (env_, j) =
                            env_.judge_of_constant_knowing_parameters(o, jl.iter().map(|j| &j.1)
                                                                                  .rev())?;
                        env = env_; j
                    },
                    _ => { // No sort-polymorphism
                        let env_ = env; let (env_, j) = env_.execute(f)?; env = env_; Cow::Owned(j)
                    },
                };
                env.judge_of_apply(f, &j, jl.iter().rev())
*/
}

impl<T, C, Ctx> Execute<Ctx> for Lambda<T, C>
    where
        Ctx: Context,
        T: ExecuteType<Ctx>,
        C: Execute<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>,
                /*let (ref name, ref c1, ref c2) = **o;
                let mut ty = Constr::Rel(0); // dummy
                let (env, _) = self.execute_type(c1, &mut ty)?;
                env.push_rel(RDecl::LocalAssum(name.clone(), c1.clone()));
                let (env, j_) = env.execute(c2)?;
                // Make sure to unwind the rel_context on success.
                // Note that we currently don't pop the rel if there was an error, even if it
                // wasn't a TypeError that consumed the env.
                if let Some(RDecl::LocalAssum(name, c1)) = env.rel_context.pop() {
                    Ok((env, Constr::Prod(ORef(Arc::from((name, c1, j_))))))
                } else { unreachable!("env should be unchanged if the execute was successful.") }*/
{
    type Type = Prod<T, <C as Execute<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>>::Type>;
}

impl<T, C, Ctx> Execute<Ctx> for Prod<T, C>
    where
        Ctx: Context,
        T: ExecuteType<Ctx>,
        C: ExecuteType<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>,
        Ctx: SortOfProduct<<T as ExecuteType<Ctx>>::Sort,
                           <C as ExecuteType<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>>::Sort>,
{
    type Type = Sort<<Ctx as SortOfProduct<<T as ExecuteType<Ctx>>::Sort,
                                           <C as ExecuteType<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>>::Sort>>::Sort>;
}
            /*Constr::Prod(ref o) => {
                let (ref name, ref c1, ref c2) = **o;
                let mut ty = Constr::Rel(0); // dummy
                let (env, varj) = self.execute_type(c1, &mut ty)?;
                env.push_rel(RDecl::LocalAssum(name.clone(), c1.clone()));
                let mut ty = Constr::Rel(0); // dummy
                let (env, varj_) = env.execute_type(c2, &mut ty)?;
                // Make sure to unwind the rel_context on success.
                // Note that we currently don't pop the rel if there was an error, even if it
                // wasn't a TypeError that consumed the env.
                env.rel_context.pop();
                let sort = env.sort_of_product(varj, varj_)?.into_owned();
                Ok((env, Constr::Sort(ORef(Arc::from(sort)))))
            },*/

pub trait ExecuteType<Ctx> where
    Ctx : Context,
    // Self: Execute<Ctx>,
    // Self::Type : JudgeOfSort/*<Ctx>*/,
{
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<Term, Ctx> ExecuteType<Ctx> for Term
    where
        Ctx : Context,
        Term : Execute<Ctx>,
        Term::Type : WhdAll<Ctx>,
        <Term::Type as WhdAll<Ctx>>::Output : TypeJudgment<Ctx>,
        /*Term : Execute<Ctx>,
        Term::Type : JudgeOfSort/*<Ctx>*/,*/
{
    type Sort = <<Term::Type as WhdAll<Ctx>>::Output as TypeJudgment<Ctx>>::Sort;//<Term::Type as JudgeOfSort>::Sort;
}

#[cfg(test)]
mod test {
    use frunk::hlist::{HCons, HList, HNil, LiftFrom, Selector};
    use frunk::indices::{Here, There};
    use super::*;

    #[derive(Generic, LabelledGeneric)]
    struct MyContext<Subs> {
        subs: Subs,
    }

    impl<Subs> RawContext for MyContext<Subs> where Subs : HList {
        type Subs = Subs;
    }

    impl<Subs> MyContext<Subs> where Subs : HList {
        fn my_judge_sort<Ty, S>(/*, x : X*/)
            where
                Ty : ExecuteType<Self, Sort = S>,
                S : JudgeOfSort,
                //Ty : ExecuteType<Self>,
                //Ty: TypeJudgment/*<Self>*/,
        {
        }

        fn my_judge_type<X, Ty, S>(/*, x : X*/)
            where
                X : Execute<Self, Type = Ty>,
                Ty : ExecuteType<Self, Sort = S>,
                S : JudgeOfSort,
                //Ty: JudgeOfSort/*<Self>*/,
        {
        }
    }

    #[test]
    fn judge_simple_rel() {
        type Ctx = MyContext<Hlist![
            Decl<Sort<Set>, Sort<Type>>,
            Assum<Sort<Set>>,
            Assum<Prod<Sort<Set>, Prod<Rel<There<Here>>, Rel<There<Here>>>>>,
            Assum<Sort<Set>>
        ]>;
        // let my_context = MyContext { subs : hlist![(), Assum { ty: Sort { sort: Set } }] };
        // let rel = Rel { index: Here };
        // my_context.my_judge::<Rel<Here>, Sort<Set>>();
        Ctx::my_judge_sort::<Sort<Set>, Type>();
        Ctx::my_judge_sort::<Rel<Here>, Type>();
        Ctx::my_judge_sort::<Rel<There<Here>>, Set>();
        Ctx::my_judge_type::<Rel<There<There<Here>>>, Prod<Sort<Set>, Prod<Rel<There<There<There<There<Here>>>>>, Rel<There<Here>>>>, Type>();
        // Nice: ∀ (X : Set) (Y : ∀ (_ : X), X), Y : Set
        MyContext::<Hlist![Assum<Prod<Rel<Here>, Rel<There<Here>>>>, Assum<Sort<Set>>]>::
            my_judge_type::<Rel<Here>, Prod<Rel<There<Here>>, Rel<There<There<Here>>>>, Set>();
        // Beelow should error: roughly equivalent to forall (X : Set) (Y : X), Y, which (in Coq)
        // errors with `the term "Y" has type "X" which should be Set, Prop or Type.`
        // Ctx::my_judge::<Prod<Rel<Here>, Rel<Here>>, Sort<Type>>();
        Ctx::my_judge_sort::<Prod<Sort<Set>, Rel<Here>>, Type>();
        Ctx::my_judge_sort::<Prod<Rel<Here>, Rel<There<Here>>>, Type>();
        Ctx::my_judge_type::<Lambda<Rel<There<Here>>, Rel<Here>>, Prod<Rel<There<Here>>, Rel<There<There<Here>>>>, Set>();
        // Below should error: would require universe larger than Type.
        // Ctx::my_judge_type::<Lambda<Rel<There<Here>>, Sort<Set>>, Prod<Rel<There<Here>>, Sort<Type>>, Type>();
        Ctx::my_judge_type::<Lambda<Rel<There<Here>>, Rel<There<There<Here>>>>, Prod<Rel<There<Here>>, Sort<Set>>, Type>();
        // Note: below test basically a duplicate
        MyContext::<Hlist![Assum<Rel<Here>>, Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Rel<There<Here>>, Rel<There<There<Here>>>>, Prod<Rel<There<Here>>, Sort<Set>>, Type>();
        MyContext::<Hlist![Assum<Rel<Here>>, Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Rel<There<Here>>, Rel<There<Here>>>, Prod<Rel<There<Here>>, Rel<There<There<Here>>>>, Set>();
        Ctx::my_judge_type::<App<Lambda<Sort<Set>, Rel<Here>>, Rel<There<Here>>>, Sort<Set>, Type>();
        Ctx::my_judge_type::<Lambda<Sort<Set>, Lambda<Rel<Here>, Rel<Here>>>, Prod<Sort<Set>, Prod<Rel<Here>, Rel<There<Here>>>>, Type>();
        Ctx::my_judge_type::<App<Lambda<Sort<Set>, Lambda<Rel<Here>, Rel<Here>>>, Rel<There<Here>>>,
                             Prod<Rel<There<Here>>, Rel<There<There<Here>>>>,
                             Set>();
        // Below requires weak head reduction to be at least partially implemented (for rels) in order to succeed.
        /* MyContext::<Hlist![Assum<Rel<Here>>, Assum<Sort<Set>>]>::
            my_judge_type::<App<App<Lambda<Sort<Set>, Lambda<Rel<Here>, Rel<Here>>>, Rel<There<Here>>>, Rel<Here>>,
                            Rel<Here>,
                            Set>(); */
        // Below should error: would require a universe larger than Type.
        // Ctx::my_judge_type::<Prod<Sort<Type>, Rel<There<Here>>>, Sort<Type>, _>();
    }
}
