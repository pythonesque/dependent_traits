use std::mem;
use std::ops::Add;
use frunk::{Generic, LabelledGeneric};
use frunk::hlist::{HCons, HList, HNil, LiftFrom, Selector};
use frunk::indices::{Here, There};
use frunk::traits::{IntoReverse};
// use frunk::prelude::*;

pub struct Inl<L> {
    l: L,
}

pub struct Inr<R> {
    r: R,
}

pub struct TSome<T> {
    t: T,
}

pub struct TNone;

pub struct True;

pub struct False;

pub trait IAnd<A> {
    type Output;
}

impl<B> IAnd<False> for B {
    type Output = False;
}

impl IAnd<True> for False {
    type Output = False;
}

impl IAnd<True> for True {
    type Output = True;
}

pub trait Equal<T> {
}

/// EqRefl
impl<T> Equal<T> for T {
}

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

/// Version of AtIndex that returns None on failure.
pub trait AtIndexOpt<Index>/* : Selector<Self::Output, Index>*/
{
    type Output;
}

impl<Head, Tail> AtIndexOpt<Here> for HCons<Head, Tail> {
    type Output = TSome<Head>;
    // fn select(&self) -> Selector<Output, Tail>
    // type Selector : Selector<, >;
}

impl<TailIndex> AtIndexOpt<There<TailIndex>> for HNil {
    type Output = TNone;
}

impl<Head, Tail, TailIndex> AtIndexOpt<There<TailIndex>> for HCons<Head, Tail>
    where Tail : AtIndexOpt<TailIndex>
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

pub trait IAdd<RHS> {
    type Output;
}

impl<M> IAdd<Here> for M {
    type Output = There<M>;

    /* fn add(self, rhs: Here) -> Self::Output {
        self
    } */
}

impl<M, N> IAdd<There<N>> for M
    where M : IAdd<N>
{
    type Output = There<<M as IAdd<N>>::Output>;

    /* fn add(self, rhs: There<M>) -> There<<Rel<M> as Add<N>>::Output>
        //Self::Output
    {
        // NOTE: Shouldn't really require unsafe (should be able to
        // construct it Peano-style as { There : rhs.there.add() }...
        // but we don't have access to the module).
        unsafe { mem::transmute(self) }
    } */
}

/// NOTE: For ISub purposes, Here means 0, not 1!
pub trait ISub<RHS> {
    type Output;
}

impl<M> ISub<Here> for M {
    type Output = M;
}

impl<N> ISub<There<N>> for Here {
    type Output = Here;
}

impl<M, N> ISub<There<N>> for There<M>
    where M : ISub<N>
{
    type Output = <M as ISub<N>>::Output;
}

/// Lifting

pub struct ElId;

/// lift of N, then apply lift Lift
pub struct ElShift<Lift, N> {
    l: Lift,
    n: N,
}

/// apply Lift to de bruijn > N
pub struct ElLift<N, Lift> {
    n: N,
    l: Lift,
}

/// Copmose a relocation of magnitude N
pub trait EShiftRec<N> {
    type Output;
}

impl<N, El, K> EShiftRec<N> for ElShift<El, K>
    where K: IAdd<N>,
          El : EShiftRec<<K as IAdd<N>>::Output>,
{
    type Output = <El as EShiftRec<<K as IAdd<N>>::Output>>::Output;
}

impl<N> EShiftRec<N> for ElId {
    type Output = ElShift<ElId, N>;
}

impl<N, K, El> EShiftRec<N> for ElLift<K, El> {
    type Output = ElShift<ElLift<K, El>, N>;
}

/// Copmose a relocation of magnitude Pred<N>
pub trait EShift<N> {
    type Output;
}

impl<El> EShift<Here> for El {
    type Output = El;
}

impl<El, N> EShift<There<N>> for El where El: EShiftRec<N> {
    type Output = <El as EShiftRec<N>>::Output;
}

/// Cross N binders
pub trait ELiftRec<N> {
    type Output;
}

impl<N> ELiftRec<N> for ElId {
    type Output = ElId;
}

impl<N, K, El> ELiftRec<N> for ElLift<K, El>
    where K: IAdd<N>,
          El : ELiftRec<<K as IAdd<N>>::Output>,
{
    type Output = <El as ELiftRec<<K as IAdd<N>>::Output>>::Output;
}

impl<N, El, K> ELiftRec<N> for ElShift<El, K> {
    type Output = ElLift<N, ElShift<El, K>>;
}

/// Cross Pred<N> binders
pub trait ELiftN<N> {
    type Output;
}

impl<El> ELiftN<Here> for El {
    type Output = El;
}

impl<N, El> ELiftN<There<N>> for El where El: ELiftRec<N> {
    type Output = <El as ELiftRec<N>>::Output;
}

/// Cross one binder
pub trait ELift {
    type Output;
}

impl<El> ELift for El where El: ELiftN<There<Here>> {
    type Output = <El as ELiftN<There<Here>>>::Output;
}

/// Relocation of de Bruijn n in an explicit lift ElLift<k, el> (aux trait, self = n - k)
pub trait RelocRelLift<N, K, El> {
    type Output;
}

/// Zero case : n - k ≤ 0 (n ≤ k)
impl<N, K, El> RelocRelLift<N, K, El> for Here
{
    type Output = N;
}

/// Succ case : n - k = ndiffk (n > k)
impl<N, K, El, NDiffK> RelocRelLift<N, K, El> for There<NDiffK>
    where
        El: RelocRel<NDiffK>,
        <El as RelocRel<NDiffK>>::Output: IAdd<K>,
{
    type Output = <<El as RelocRel<NDiffK>>::Output as IAdd<K>>::Output;
}

/// Relocation of de Bruijn n in an explicit lift
pub trait RelocRel<N> {
    type Output;
}

impl<N> RelocRel<N> for ElId {
    type Output = N;
}

impl<N, K, El> RelocRel<N> for ElLift<K, El>
    where
        There<N> : ISub<There<K>>,
        <There<N> as ISub<There<K>>>::Output : RelocRelLift<N, K, El>,
{
    type Output = <<There<N> as ISub<There<K>>>::Output as RelocRelLift<N, K, El>>::Output;
}

impl<N, El, K> RelocRel<N> for ElShift<El, K>
    where
        N : IAdd<K>,
        El : RelocRel<<N as IAdd<K>>::Output>,
{
    type Output = <El as RelocRel<<N as IAdd<K>>::Output>>::Output;
}

/// Substitutions

/// ESID(n)    = %n END   bounded identity
pub struct EsId<N> {
    /// NOTE: n = pred N
    n: N,
}

/// CONS(t,S)  = (S.t)    parallel substitution
pub struct EsCons<T,S> {
    t: T,
    s: S,
}

/// SHIFT(n,S) = (^n o S) terms in S are relocated with n vars
pub struct EsShift<N, S> {
    n: N,
    s: S,
}

/// LIFT(n,S) = (%n S) stands for ((^n o S).n...1)
pub struct EsLift<N, S> {
    n: N,
    s: S,
}

pub trait SubsCons<X> {
    type Output;
}

impl<X, S> SubsCons<X> for S {
    type Output = EsCons<X, S>;
}

pub trait SubsLiftN2<N> {
    type Output;
}

/// bounded identity lifted extends by p
///
/// Here + N = N; There P + N = P + N; thn add 1, so it
/// amounts to just adding P.
impl<N, P> SubsLiftN2<N> for EsId<P> where P : IAdd<N> {
    type Output = EsId<<P as IAdd<N>>::Output>;
}

impl<N, P, LEnv> SubsLiftN2<N> for EsLift<P, LEnv> where P : IAdd<N> {
    type Output = EsLift<<P as IAdd<N>>::Output, LEnv>;
}

impl<N, X, LEnv> SubsLiftN2<N> for EsCons<X, LEnv> {
    type Output = EsLift<N, EsCons<X, LEnv>>;
}

impl<N, K, LEnv> SubsLiftN2<N> for EsShift<K, LEnv> {
    type Output = EsLift<N, EsShift<K, LEnv>>;
}

pub trait SubsLift {
    type Output;
}

impl<A> SubsLift for A where A : SubsLiftN2<Here> {
    type Output = <A as SubsLiftN2<Here>>::Output;
}

pub trait SubsLiftN<N> {
    type Output;
}

/// lift by 0
impl<A> SubsLiftN<Here> for A {
    type Output = A;
}

/// lift by S n
impl<N, A> SubsLiftN<There<N>> for A where A : SubsLiftN2<N> {
    type Output = <A as SubsLiftN2<N>>::Output;
}

/// shift by N
pub trait SubsShft<N> {
    type Output;
}

impl<N, K, S1> SubsShft<N> for EsShift<K, S1> where K : IAdd<N> {
    type Output = EsShift<<K as IAdd<N>>::Output, S1>;
}

impl<N, K> SubsShft<N> for EsId<K> {
    type Output = EsShift<N, EsId<K>>;
}

impl<N, X, S1> SubsShft<N> for EsCons<X, S1> {
    type Output = EsShift<N, EsCons<X, S1>>;
}

impl<N, K, S1> SubsShft<N> for EsLift<K, S1> {
    type Output = EsShift<N, EsLift<K, S1>>;
}

/// KDiffN = K - N
pub trait ExpRelLift<Lams, K, KDiffN> {
    type Output;
}

/// K - N ≤ 0 → K ≤ N (Lams = Here, i.e. Lams = 0)
impl<K, N, L> ExpRelLift<Here, K, Here> for EsLift<N, L> {
    type Output = Inr<(K, Here)>;
}

/// K - N ≤ 0 → K ≤ N (Lams = There Lams', i.e. Lams = Lams')
impl<Lams, K, N, L> ExpRelLift<There<Lams>, K, Here> for EsLift<N, L> where Lams : IAdd<K> {
    type Output = Inr<(<Lams as IAdd<K>>::Output, Here)>;
}

/// K - N > 0 → K > N
impl<Lams, K, KDiffN, N, L> ExpRelLift<Lams, K, There<KDiffN>> for EsLift<N, L>
    where
        N : IAdd<Lams>,
        L : ExpRel<<N as IAdd<Lams>>::Output, KDiffN>
{
    type Output = <L as ExpRel<<N as IAdd<Lams>>::Output, KDiffN>>::Output;
}

/// KDiffN = K - N
pub trait ExpRelId<Lams, K, KDiffN> {
    type Output;
}

/// K - N ≤ 0 → K ≤ N (Lams = Here, i.e. Lams = 0)
impl<K, N> ExpRelId<Here, K, Here> for EsId<N> {
    type Output = Inr<(K, Here)>;
}

/// K - N ≤ 0 → K ≤ N (Lams = There Lams', i.e. Lams = Lams')
impl<Lams, K, N> ExpRelId<There<Lams>, K, Here> for EsId<N> where Lams : IAdd<K> {
    type Output = Inr<(<Lams as IAdd<K>>::Output, Here)>;
}

/// K - N > 0 → K > N (Lams = Here, i.e. Lams = 0)
impl<K, KDiffN, N> ExpRelId<Here, K, There<KDiffN>> for EsId<N> {
    type Output = Inr<(K, There<KDiffN>)>;
}

/// K - N > 0 → K > N (Lams = There Lams', i.e. Lams = Lams')
impl<Lams, K, KDiffN, N> ExpRelId<There<Lams>, K, There<KDiffN>> for EsId<N> where Lams : IAdd<K> {
    type Output = Inr<(<Lams as IAdd<K>>::Output, There<KDiffN>)>;
}

/// Expands de Bruijn k in the explicit substitution subs
/// lams accumulates de shifts to perform when retrieving the i-th value
/// the rules used are the following:
///
///    [id]k       --> k
///    [S.t]1      --> t
///    [S.t]k      --> [S](k-1)  if k > 1
///    [^n o S] k  --> [^n]([S]k)
///    [(%n S)] k  --> k         if k <= n
///    [(%n S)] k  --> [^n]([S](k-n))
///
/// The result is either (Inl(lams,v)) when the variable is
/// substituted by value [v] under lams binders (i.e. v *has* to be
/// shifted by lams), or (Inr (k',p)) when the variable k is just relocated
/// as k'; p is Here if the variable points inside subs and There(k) if the
/// variable points k bindings beyond subs (cf argument of ESID).
pub trait ExpRel<Lams, K> {
    type Output;
}
/*let rec exp_rel lams k subs =
  match subs with
    | CONS (def,_) when k <= Array.length def
                           -> Inl(lams,def.(Array.length def - k))
    | CONS (v,l)           -> exp_rel lams (k - Array.length v) l
    | LIFT (n,_) when k<=n -> Inr(lams+k,None)
    | LIFT (n,l)           -> exp_rel (n+lams) (k-n) l
    | SHIFT (n,s)          -> exp_rel (n+lams) k s
    | ESID n when k<=n     -> Inr(lams+k,None)
    | ESID n               -> Inr(lams+k,Some (k-n))*/

/// k ≤ 1
impl<Lams, Def, L> ExpRel<Lams, Here> for EsCons<Def, L>
{
    type Output = Inl<(Lams, Def)>;
}

/// k > 1
impl<Lams, K, Def, L> ExpRel<Lams, There<K>> for EsCons<Def, L> where L : ExpRel<Lams, K> {
    type Output = <L as ExpRel<Lams, K>>::Output;
}

impl<Lams, K, N, L> ExpRel<Lams, K> for EsLift<N, L>
    where
        There<K> : ISub<There<N>>,
        Self : ExpRelLift<Lams, K, <There<K> as ISub<There<N>>>::Output>,
{
    type Output = <Self as ExpRelLift<Lams, K, <There<K> as ISub<There<N>>>::Output>>::Output;
}

impl<Lams, K, N, S> ExpRel<Lams, K> for EsShift<N, S>
    where
        N : IAdd<Lams>,
        S : ExpRel<<N as IAdd<Lams>>::Output, K>,
{
    type Output = <S as ExpRel<<N as IAdd<Lams>>::Output, K>>::Output;
}

impl<Lams, K, N> ExpRel<Lams, K> for EsId<N>
    where
        There<K> : ISub<N>,
        Self : ExpRelId<Lams, K, <There<K> as ISub<N>>::Output>,
{
    type Output = <Self as ExpRelId<Lams, K, <There<K> as ISub<N>>::Output>>::Output;
}

pub trait ExpandRel<K> {
    type Output;
}

impl<K, Subs> ExpandRel<K> for Subs where Subs : ExpRel<Here, K> {
    type Output = <Subs as ExpRel<Here, K>>::Output;
}

    //Selector<FromTail, There<TailIndex>> for HCons<Head, Tail>

/* #[derive(Generic, LabelledGeneric)]
pub struct Context<Subs : HList> {
    subs: Subs,
} */

pub trait RawContext {
    type Subs;
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

/// The generic lifting function
pub trait ExLiftN<El> {
    type Output;
}

impl<El, T, C> ExLiftN<El> for Prod<T, C>
    where
        T: ExLiftN<El>,
        El : ELift,
        C: ExLiftN<<El as ELift>::Output>,
{
    type Output = Prod<<T as ExLiftN<El>>::Output, <C as ExLiftN<<El as ELift>::Output>>::Output>;
}

impl<El, T, B> ExLiftN<El> for Lambda<T, B>
    where
        T: ExLiftN<El>,
        El : ELift,
        B: ExLiftN<<El as ELift>::Output>,
{
    type Output = Lambda<<T as ExLiftN<El>>::Output, <B as ExLiftN<<El as ELift>::Output>>::Output>;
}

impl<El, F, A> ExLiftN<El> for App<F, A>
    where
        F: ExLiftN<El>,
        A: ExLiftN<El>,
{
    type Output = App<<F as ExLiftN<El>>::Output, <A as ExLiftN<El>>::Output>;
}

impl<El, S> ExLiftN<El> for Sort<S> {
    type Output = Self;
}

/// Lifting

impl<El, Index> ExLiftN<El> for Rel<Index>
    where
        El : RelocRel<Index>,
{
    type Output = Rel<<El as RelocRel<Index>>::Output>;
}

/// Lifting the binding depth across k bindings
pub trait LiftN<K, N> {
    type Output;
}

impl<K, N, T> LiftN<K, N> for T
    where
        ElId : EShift<There<K>>,
        // NOTE: ELiftN expects N+1, so it lifts by N-1, which is what we want here.
        <ElId as EShift<There<K>>>::Output : ELiftN<N>,
        T : ExLiftN<<<ElId as EShift<There<K>>>::Output as ELiftN<N>>::Output>,
{
    type Output = <T as ExLiftN<<<ElId as EShift<There<K>>>::Output as ELiftN<N>>::Output>>::Output;
}

pub trait Lift<Index> : LiftN</*Here, Index*/Index, Here>
{
    type Output;
}

impl<T, Index> Lift<Index> for T where T : LiftN</*Here, Index*/Index, Here>
{
    type Output = <T as LiftN</*Here, Index*/Index, Here>>::Output;
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
    type Output = Lambda<<T as SubstRec<N, LamV, LV>>::Output, <B as SubstRec<There<N>, LamV, LV>>::Output>;
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
impl<N, LamV, LV, IndexDiffK, LVDiff, Index> SubstRel2<N, LamV, LV, IndexDiffK, There<LVDiff>> for Rel</*There<*/Index/*>*/>
    where
        Index : ISub<LV>,
{
    type Output = Rel<<Index as ISub<LV>>::Output>;
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
        There<IndexDiffK> : ISub<LV>,
        // Note that if lv < k - depth, depth < k - lv, so k - lv > 0; therefore,
        // since subtraction normally returns output + 1, and we know the output is
        // positive, we can get the real output by subtracting 1 from k first (it
        // won't mess up at 0 because (k - 1) - lv ≥ 0).
        // Even though it's not always necessary, we also compute k - lv here to
        // be able to extract the There pattern (if k - depth ≤ lv)
        Rel<Index> : SubstRel2<N, LamV, LV, IndexDiffK, <There<IndexDiffK> as ISub<LV>>::Output>,
        /*  else if k-depth <= lv then lift_substituend depth lamv.(k-depth-1)

         */
        // Self : IAdd<N>,
{
    type Output = <Self as SubstRel2<N, LamV, LV, IndexDiffK, <There<IndexDiffK> as ISub<LV>>::Output>>::Output;
}

impl<N, LamV, LV, Index> SubstRec<N, LamV, LV> for Rel<Index>
    where
        // NOTE: N is "really" There<N'>, where N' is what we care about.
        There<Index> : ISub<N>,
        // Compute the necessary relocation.
        Self: SubstRel<N, LamV, LV, <There<Index> as ISub<N>>::Output>,
{
    type Output = <Self as SubstRel<N, LamV, LV, <There<Index> as ISub<N>>::Output>>::Output;
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
pub trait SubstNMany<LamV, N> {
    type Output;
}

impl<N, C> SubstNMany<HNil, N> for C
{
    type Output = C;
}

/// FIXME: Pass around PeanoLen-1 (which is actually the proper length).
impl<Lam, LamV, N, C> SubstNMany<HCons<Lam, LamV>, N> for C
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
    type Output = <C as SubstNMany<Hlist![Lam], Here>>::Output;
}
/*
    pub fn subst1(&self, lam: &Constr) -> IdxResult<Constr> {
        let lamv = [Substituend::make(lam)];
        self.substn_many(&lamv, None)
    }
*/

pub trait Reds {
    type Delta;
}

pub struct BetaDeltaIota;

pub struct BetaIotaZeta;

impl Reds for BetaDeltaIota {
    type Delta = True;
}

impl Reds for BetaIotaZeta {
    type Delta = False;
}

pub trait Infos {
    type Flags : Reds;
    type Rels;
}

pub trait RefValueCacheRel<N> {
    type Output;
}

/// Rel out of bounds (NOTE: should this actually be an error?)
impl<N> RefValueCacheRel<N> for TNone {
    type Output = TNone;
}

/// Rel in bounds, but an Assum, not a Decl (hence no body).
impl<Type, N> RefValueCacheRel<N> for TSome<Assum<Type>> {
    type Output = TNone;
}

/// Rel in bounds, and a Decl (hence has body)
impl<Body, Type, N> RefValueCacheRel<N> for TSome<Decl<Body, Type>>
    where
        Body : Lift<N>,
        <Body as Lift<N>>::Output : Inject,
{
    type Output = TSome<<<Body as Lift<N>>::Output as Inject>::Output>;
}

pub trait RefValueCache<Ref> {
    type Output;
}

impl<Info : Infos, N> RefValueCache<Rel<N>> for Info
    where
        Info::Rels : AtIndexOpt<N>,
        <Info::Rels as AtIndexOpt<N>>::Output : RefValueCacheRel<N>,
{
    type Output = <<Info::Rels as AtIndexOpt<N>>::Output as RefValueCacheRel<N>>::Output;
}

/// FVal(c) represents the constr c.
/// c must be in normal form and neutral (i.e. not a lambda, a construct or a
/// (co)fix, because they may produce redexes by applying them,
/// or putting them in a case)
pub struct FVal<C> {
    c: C,
}

/// FFlex(c) represents the RelKey / ConstKey c.
///
/// NOTE: Might be able to replace FFlex(c) with FCbn(c, EsId(Here)), since evaluating in that
/// (empty) environment is essentially what we do when grabbing the contents of the flex.
pub struct FFlex<C> {
    c: C,
}

/// FStk(v,stk) represents an irreductible value [v] in the stack [stk].
/// (Note that [v] is a WhdValue and [Stk] is a *reversed* Stack; the
/// reversal is necessary to emulate the behavior of Zip).
pub struct FStk<V, Stk> {
    v: V,
    stk: Stk,
}

/// FCbn(t,S) is the term [S]t. It is used to delay evaluation.
/// (Note that [t] is a Constr and [S] is a substitution).
pub struct FCbn<T, S> {
    t: T,
    s: S,
}

/// ZApp is a delayed application of the head to A on a Stack.
pub struct ZApp<A> {
    a: A,
}

/// ZShift is a delayed shift of the head by K on a Stack.
///
/// NOTE: Currently K is the real shift, but we could turn it into K = Pred<K'> with K' the real
/// shift if needed (this would allow shifts by 0).
pub struct ZShift<K> {
    k: K,
}

/// WhdAppendStack appends V to stack Self
pub trait WhdAppendStack<V> {
    type Output;
}

impl<V, S> WhdAppendStack<V> for S {
    type Output = HCons<ZApp<V>, S>;
}

/// StkShift adds a delayed shift by N to stack Self
/// (collapses shifts in the stack).
pub trait StkShift<N> {
    type Output;
}

impl<N, K, S> StkShift<N> for HCons<ZShift<K>, S> where N : IAdd<K> {
    type Output = HCons<ZShift<<N as IAdd<K>>::Output>, S>;
}

impl<N, A, S> StkShift<N> for HCons<ZApp<A>, S> {
    type Output = HCons<ZShift<N>, Self>;
}

impl<N> StkShift<N> for HNil {
    type Output = HCons<ZShift<N>, Self>;
}

/// Lifting by K. Preserves sharing where theoretically useful (norm = Red).
pub trait WhdLft<K> {
    type Output;
}

/* /// Lifting a stack by K: add the lift to the stack. NOTE: need to reverse this!
impl<K, V, S> WhdLft<K> for FStk<V, S> where S : StkShift<K> {
    type Output = <S as StkShift<K>>::Output;
}

/// Lifting a value by K: just lift the value directly using exlittn (it's normal
/// so this is fine).
impl<K, V, S> WhdLft<K> for FStk<V, S> where S : StkShift<K> {
    type Output = <S as StkShift<K>>::Output;
} */

impl<K, V> WhdLft<K> for V {
    type Output = FStk<V, Hlist![ZShift<K>]>;
}

/// WhdLift<K> lifts Self by K' if K = There K', otherwise does not lift.
pub trait WhdLift<K> {
    type Output;
}

impl<F> WhdLift<Here> for F {
    type Output = F;
}

impl<K, F> WhdLift<There<K>> for F where F : WhdLft<K> {
    type Output = <F as WhdLft<K>>::Output;
}

/// Turn a rel I into a closed value, where Self is the result
/// of running ExpandRel<I> for environment E.
pub trait ClosRel<I> {
    type Output;
}

impl<I, N, MT> ClosRel<I> for Inl<(N, MT)> where MT : WhdLift<N> {
    type Output = <MT as WhdLift<N>>::Output;
}

/// Note: currently ExpandRel returns the real K for Inr cases, rather than
/// There K; but we could also change ExpandRel to be a bit simpler and have
/// Inr only accept There K.
impl<I, K> ClosRel<I> for Inr<(K, Here)> {
    type Output = FVal<Rel<K>>;
}

/// See above comment
///
/// NOTE: k-p guaranteed non-negative.
impl<I, K, P> ClosRel<I> for Inr<(K, There<P>)>
    where
        There<K> : ISub<There<P>>,
        FFlex<Rel<P>> : WhdLift<<There<K> as ISub<There<P>>>::Output>,
{
    type Output = <FFlex<Rel<P>> as WhdLift<<There<K> as ISub<There<P>>>::Output>>::Output;
}

/// Optimization: do not enclose variables in a closure.
/// Makes variable access much faster.
/// E is the environment.
pub trait MkClos<E> {
    type Output;
}

impl<E, I> MkClos<E> for Rel<I>
    where
        E : ExpandRel<I>,
        <E as ExpandRel<I>>::Output : ClosRel<I>,
{
    type Output = <<E as ExpandRel<I>>::Output as ClosRel<I>>::Output;
}

impl<E, S> MkClos<E> for Sort<S> {
    type Output = FVal<Sort<S>>;
}

impl<E, T, B> MkClos<E> for Lambda<T, B> {
    type Output = FCbn<Lambda<T, B>, E>;
}

impl<E, T, C> MkClos<E> for Prod<T, C> {
    type Output = FCbn<Prod<T, C>, E>;
}

impl<E, F, A> MkClos<E> for App<F, A> {
    type Output = FCbn<App<F, A>, E>;
}

/// The inverse of mk_clos: move Self back to constr under Lfts lifting environment.
pub trait ToConstr<Lfts> {
    type Output;
}

/// Values in normal form just get lifted to the corresponding Constr.
impl<Lfts, C> ToConstr<Lfts> for FVal<C> where C : ExLiftN<Lfts> {
    type Output = <C as ExLiftN<Lfts>>::Output;
}

/// FFlex values also just get lifted to the corresponding Constr (the difference mostly
/// matters for conversion, which wants to compare RelKeys for equality without
/// considering the lifting environment because it knows that if they are equal unlifted
/// their bodies will also be equal; while for interior substitutions, that's not the case
/// since they are not shared between the two terms, and they must be exactly identical).
impl<Lfts, C> ToConstr<Lfts> for FFlex<C> where C : ExLiftN<Lfts> {
    type Output = <C as ExLiftN<Lfts>>::Output;
}

impl<Lfts, F, A, Env> ToConstr<Lfts> for FCbn<App<F, A>, Env>
    where
        F : MkClos<Env>,
        <F as MkClos<Env>>::Output : ToConstr<Lfts>,
        A : MkClos<Env>,
        <A as MkClos<Env>>::Output : ToConstr<Lfts>,
{
    type Output = App<<<F as MkClos<Env>>::Output as ToConstr<Lfts>>::Output,
                      <<A as MkClos<Env>>::Output as ToConstr<Lfts>>::Output>;
}

impl<Lfts, T, B, Env> ToConstr<Lfts> for FCbn<Lambda<T, B>, Env>
    where
        T : MkClos<Env>,
        <T as MkClos<Env>>::Output : ToConstr<Lfts>,
        Env : SubsLift,
        B : MkClos<<Env as SubsLift>::Output>,
        Lfts : ELift,
        <B as MkClos<<Env as SubsLift>::Output>>::Output : ToConstr<<Lfts as ELift>::Output>,
{
    type Output = Lambda<<<T as MkClos<Env>>::Output as ToConstr<Lfts>>::Output,
                         <<B as MkClos<<Env as SubsLift>::Output>>::Output as
                          ToConstr<<Lfts as ELift>::Output>>::Output>;
}

impl<Lfts, T, C, Env> ToConstr<Lfts> for FCbn<Prod<T, C>, Env>
    where
        T : MkClos<Env>,
        <T as MkClos<Env>>::Output : ToConstr<Lfts>,
        Env : SubsLift,
        C : MkClos<<Env as SubsLift>::Output>,
        Lfts : ELift,
        <C as MkClos<<Env as SubsLift>::Output>>::Output :
            ToConstr<<Lfts as ELift>::Output>,
{
    type Output = Prod<<<T as MkClos<Env>>::Output as ToConstr<Lfts>>::Output,
                       <<C as MkClos<<Env as SubsLift>::Output>>::Output as
                        ToConstr<<Lfts as ELift>::Output>>::Output>;
}

/// For an empty stack, just apply ToConstr to the value at the stack head.
impl<Lfts, V> ToConstr<Lfts> for FStk<V, HNil>
    where
        V : ToConstr<Lfts>,
{
    type Output = <V as ToConstr<Lfts>>::Output;
}

/// For an app (reversed) stack, first run Stk on F, then apply the result to A.
impl<Lfts, F, A, Stk> ToConstr<Lfts> for FStk<F, HCons<ZApp<A>, Stk>>
    where
        FStk<F, Stk> : ToConstr<Lfts>,
        A : ToConstr<Lfts>,
{
    type Output = App<<FStk<F, Stk> as ToConstr<Lfts>>::Output, <A as ToConstr<Lfts>>::Output>;
}

/// For a shift (reversed) stack, shift Lfts by K, then run Stk on V with the resulting Lfts.
impl<Lfts, A, K, Stk> ToConstr<Lfts> for FStk<A, HCons<ZShift<K>, Stk>>
    where
        Lfts : EShift<There<K>>,
        FStk<A, Stk> : ToConstr<<Lfts as EShift<There<K>>>::Output>,
{
    type Output = <FStk<A, Stk> as ToConstr<<Lfts as EShift<There<K>>>::Output>>::Output;
}

/// fapp_stack transforms a value and a stack into the reversed stack applied to the value,
/// generally for use in to_constr.  M is the value and Self is the stack.
pub trait FAppStack<M> {
    type Output;
}

/// For now, FAppStack just reverses and doesn't do anything else (like unlocking updates).
impl<M, Stk : IntoReverse> FAppStack<M> for Stk {
    type Output = FStk<M, <Stk as IntoReverse>::Output>;
}

/// Eta expansion: add a reference to implicit surrounding lambda at end of stack
pub trait EtaExpandStack {
    type Output;
}

/// We append rather than use explicit induction.
impl<Stk> EtaExpandStack for Stk
    where
        Stk : Add<Hlist![ZShift<Here>, ZApp<FVal<Rel<Here>>>]>,
{
    type Output = Stk::Output;
}

/// A machine that inspects the head of a term until it finds an
/// atom or a subterm that may produce a redex (abstraction,
/// constructor, cofix, letin, constant), or a neutral term (product,
/// inductive)
///
/// Self is Info, term is M, stack is Stk.  Returned head is Head, returned stack is Stack.
///
/// For FStk terms with reversed stacks, we just move elements from the reversed stack to the
/// non-reversed one.
pub trait Knh<M, Stk> {
    type Head;
    type Stack;
}

/// For FStk terms with an empty stack, we just run knh on the head.
impl<A, Stk, Info> Knh<FStk<A, HNil>, Stk> for Info where Info : Knh<A, Stk> {
    type Head = <Info as Knh<A, Stk>>::Head;
    type Stack = <Info as Knh<A, Stk>>::Stack;
}

/// For FStk terms with a zshift k, we shift the current stack by k and rerun with
/// the stack tail.
impl<M, K, A, Stk, Info> Knh<FStk<M, HCons<ZShift<K>, A>>, Stk> for Info
    where
        Stk : StkShift<K>,
        Info : Knh<FStk<M, A>, <Stk as StkShift<K>>::Output>,
{
    type Head = <Info as Knh<FStk<M, A>, <Stk as StkShift<K>>::Output>>::Head;
    type Stack = <Info as Knh<FStk<M, A>, <Stk as StkShift<K>>::Output>>::Stack;
}

/// For FStk terms with a zapp b, we append b to the current stack and rerun with
/// the stack tail.
impl<M, B, A, Stk, Info> Knh<FStk<M, HCons<ZApp<B>, A>>, Stk> for Info
    where
        Stk : WhdAppendStack<B>,
        Info : Knh<FStk<M, A>, <Stk as WhdAppendStack<B>>::Output>,
{
    type Head = <Info as Knh<FStk<M, A>, <Stk as WhdAppendStack<B>>::Output>>::Head;
    type Stack = <Info as Knh<FStk<M, A>, <Stk as WhdAppendStack<B>>::Output>>::Stack;
}

/// For FCbn terms, we run knht.
impl<T, E, Stk, Info> Knh<FCbn<T, E>, Stk> for Info where Info : Knht<E, T, Stk> {
    type Head = <Info as Knht<E, T, Stk>>::Head;
    type Stack = <Info as Knht<E, T, Stk>>::Stack;
}

/// For FVal terms, we return.
impl<V, Stk, Info> Knh<FVal<V>, Stk> for Info {
    type Head = FVal<V>;
    type Stack = Stk;
}

/// For FFlex terms, we return.
impl<C, Stk, Info> Knh<FFlex<C>, Stk> for Info {
    type Head = FFlex<C>;
    type Stack = Stk;
}

/// The same as knh for pure terms.
///
/// Self is Info, env is E, term is M, stack is Stk.
/// Returned head is Head, returned stack is Stack.
pub trait Knht<E, T, Stk> {
    type Head;
    type Stack;
}

impl<E, A, B, Stk, Info> Knht<E, App<A, B>, Stk> for Info
    where
        B : MkClos<E>,
        Stk : WhdAppendStack<<B as MkClos<E>>::Output>,
        Info : Knht<E, A, <Stk as WhdAppendStack<<B as MkClos<E>>::Output>>::Output>,
{
    type Head =
        <Info as Knht<E, A, <Stk as WhdAppendStack<<B as MkClos<E>>::Output>>::Output>>::Head;
    type Stack =
        <Info as Knht<E, A, <Stk as WhdAppendStack<<B as MkClos<E>>::Output>>::Output>>::Stack;
}

/// NOTE: This is the only Knht that can yield a FStk; as a result, we can assume
/// that we don't see an FStk in knr (since we call knh, which takes care of FStks).
impl<E, N, Stk, Info> Knht<E, Rel<N>, Stk> for Info
    where
        /* E : ExpandRel<N>,
        <E as ExpandRel<N>>::Output : ClosRel<N>,
        Info : Knh<<<E as ExpandRel<N>>::Output as ClosRel<N>>::Output, Stk>, */
        Rel<N> : MkClos<E>,
        Info : Knh<<Rel<N> as MkClos<E>>::Output, Stk>,
{
    /* type Head = <Info as Knh<E, <<E as ExpandRel<N>>::Output as ClosRel<N>>::Output, Stk>>::Head;
    type Stack = <Info as Knh<E, <<E as ExpandRel<N>>::Output as ClosRel<N>>::Output, Stk>>::Stack; */
    type Head = <Info as Knh<<Rel<N> as MkClos<E>>::Output, Stk>>::Head;
    type Stack = <Info as Knh<<Rel<N> as MkClos<E>>::Output, Stk>>::Stack;
}

impl<E, T, B, Stk, Info>
    Knht<E, Lambda<T, B>, Stk> for Info where Lambda<T, B> : MkClos<E> {
    type Head = <Lambda<T, B> as MkClos<E>>::Output;
    type Stack = Stk;
}

impl<E, T, C, Stk, Info> Knht<E, Prod<T, C>, Stk> for Info where Prod<T, C> : MkClos<E> {
    type Head = <Prod<T, C> as MkClos<E>>::Output;
    type Stack = Stk;
}

impl<E, S, Stk, Info> Knht<E, Sort<S>, Stk> for Info where Sort<S> : MkClos<E> {
    type Head = <Sort<S> as MkClos<E>>::Output;
    type Stack = Stk;
}

/// Decides whether to continue expanding a FFlex or not based on the result of RefValueCache.
///
/// Self is Info, initial FFlex value is C, RefValueCache<C> result is V, stack is Stk.
/// Returned head is Head, returned stack is Stack.
pub trait KnrFlex2<C, V, Stk> {
    type Head;
    type Stack;
}

/// If RefValueCache<C> is None, return FFlex<C> and Stk unchanged.
impl<C, Stk, Info> KnrFlex2<C, TNone, Stk> for Info {
    type Head = FFlex<C>;
    type Stack = Stk;
}

/// If RefValueCache<C> is TSome<V>, run kni on V.
impl<C, V, Stk, Info> KnrFlex2<C, TSome<V>, Stk> for Info where Info : Kni<V, Stk> {
    type Head = <Info as Kni<V, Stk>>::Head;
    type Stack = <Info as Kni<V, Stk>>::Stack;
}

/// Knr for FFlex<C>, where Delta is the delta flag for Self.
pub trait KnrFlex<C, Stk, Delta> {
    type Head;
    type Stack;
}

/// For a FFlex C, we look up C in our local environment and kni (if Delta).
impl<C, Stk, Info> KnrFlex<C, Stk, True> for Info
    where
        Info : RefValueCache<C>,
        Info : KnrFlex2<C, <Info as RefValueCache<C>>::Output, Stk>,
{
    type Head = <Info as KnrFlex2<C, <Info as RefValueCache<C>>::Output, Stk>>::Head;
    type Stack = <Info as KnrFlex2<C, <Info as RefValueCache<C>>::Output, Stk>>::Stack;
}

/// For a FFlex C, we return the FFlex (if !Delta).
impl<C, Stk, Info> KnrFlex<C, Stk, False> for Info {
    type Head = FFlex<C>;
    type Stack = Stk;
}

/// Computes a weak head normal form from the result of knh.
/// Self is Info, term is M, stack is Stk.
/// Returned head is Head, returned stack is Stack.
pub trait Knr<M, Stk> {
    type Head;
    type Stack;
}

/// For a FVal C, we return C and the stack unchanged.
impl<C, Stk, Info> Knr<FVal<C>, Stk> for Info {
    type Head = FVal<C>;
    type Stack = Stk;
}

/// For a FFlex C, we look up C in our local environment and kni (if Delta).
impl<C, Stk, Info : Infos> Knr<FFlex<C>, Stk> for Info
    where
        Info : KnrFlex<C, Stk, <<Info as Infos>::Flags as Reds>::Delta>,
{
    type Head = <Info as KnrFlex<C, Stk, <Info::Flags as Reds>::Delta>>::Head;
    type Stack = <Info as KnrFlex<C, Stk, <Info::Flags as Reds>::Delta>>::Stack;
}

/// For an empty stack with a FCbn Lambda, we return the Cbn and stack unaltered.
impl<T, B, E, Info> Knr<FCbn<Lambda<T, B>, E>, HNil> for Info {
    type Head = FCbn<Lambda<T, B>, E>;
    type Stack = HNil;
}

/// For a shift stack with a FCbn Lambda, we apply the shift to the Cbn environment.
impl<T, B, E, K, S, Info> Knr<FCbn<Lambda<T, B>, E>, HCons<ZShift<K>, S>> for Info
    where
        E : SubsShft<K>,
        Info : Knr<FCbn<Lambda<T, B>, <E as SubsShft<K>>::Output>, S>,
{
    type Head = <Info as Knr<FCbn<Lambda<T, B>, <E as SubsShft<K>>::Output>, S>>::Head;
    type Stack = <Info as Knr<FCbn<Lambda<T, B>, <E as SubsShft<K>>::Output>, S>>::Stack;
}

/// For an app stack with a FCbn Lambda, we cons the app to the Cbn environment and knit.
impl<T, B, E, A, S, Info> Knr<FCbn<Lambda<T, B>, E>, HCons<ZApp<A>, S>> for Info
    where
        E : SubsCons<A>,
        Info : Knit<<E as SubsCons<A>>::Output, B, S>,
{
    type Head = <Info as Knit<<E as SubsCons<A>>::Output, B, S>>::Head;
    type Stack = <Info as Knit<<E as SubsCons<A>>::Output, B, S>>::Stack;
}

impl<T, C, E, Stk, Info> Knr<FCbn<Prod<T, C>, E>, Stk> for Info {
    type Head = FCbn<Prod<T, C>, E>;
    type Stack = Stk;
}

/// Computes the weak head normal form of a term
pub trait Kni<M, Stk> {
    type Head;
    type Stack;
}

impl<M, Stk, Info> Kni<M, Stk> for Info
    where
        Info : Knh<M, Stk>,
        Info : Knr<<Info as Knh<M, Stk>>::Head, <Info as Knh<M, Stk>>::Stack>,
{
    type Head = <Info as Knr<<Info as Knh<M, Stk>>::Head, <Info as Knh<M, Stk>>::Stack>>::Head;
    type Stack = <Info as Knr<<Info as Knh<M, Stk>>::Head, <Info as Knh<M, Stk>>::Stack>>::Stack;
}

/// Computes the weak head normal form of a pure term.
pub trait Knit<E, T, Stk> {
    type Head;
    type Stack;
}

impl<E, T, Stk, Info> Knit<E, T, Stk> for Info
    where
        Info : Knht<E, T, Stk>,
        Info : Knr<<Info as Knht<E, T, Stk>>::Head, <Info as Knht<E, T, Stk>>::Stack>,
{
    type Head =
        <Info as Knr<<Info as Knht<E, T, Stk>>::Head, <Info as Knht<E, T, Stk>>::Stack>>::Head;
    type Stack =
        <Info as Knr<<Info as Knht<E, T, Stk>>::Head, <Info as Knht<E, T, Stk>>::Stack>>::Stack;
}

pub trait Kh<V, Stk> {
    type Output;
}

impl<V, Stk, Info> Kh<V, Stk> for Info
    where
        Info : Kni<V, Stk>,
        <Info as Kni<V, Stk>>::Stack : FAppStack<<Info as Kni<V, Stk>>::Head>,
{
    type Output = <<Info as Kni<V, Stk>>::Stack as FAppStack<<Info as Kni<V, Stk>>::Head>>::Output;
}

/// Weak reduction
pub trait WhdVal<V> {
    type Output;
}

impl<V, Info> WhdVal<V> for Info
    where
        Info : Kh<V, HNil>,
        <Info as Kh<V, HNil>>::Output : ToConstr<ElId>,
{
    type Output = <<Info as Kh<V, HNil>>::Output as ToConstr<ElId>>::Output;
}

pub trait Inject {
    type Output;
}

impl<T> Inject for T where T : MkClos<EsId<Here>> {
    type Output = T::Output;
}

pub trait WhdStack<M, Stk> {
    type Head;
    type Stack;
}

impl<M, Stk, Info> WhdStack<M, Stk> for Info where Info : Kni<M, Stk>,
{
    type Head = <Info as Kni<M, Stk>>::Head;
    type Stack = <Info as Kni<M, Stk>>::Stack;
}

pub trait CreateClosInfos<Flags> {
    type Info;
}

pub struct ClosInfos<Flags, Rels> {
    flags: Flags,
    rels: Rels,
}

impl<Flags : Reds, Rels> Infos for ClosInfos<Flags, Rels> {
    type Flags = Flags;
    type Rels = Rels;
}

impl<Flags, Env : Context> CreateClosInfos<Flags> for Env {
    type Info = ClosInfos<Flags, Env::Subs>;
}

/// Compute the lift to be performed on a term placed in a given stack (Self)
pub trait ElStack<El> {
    type Output;
}

impl<El> ElStack<El> for HNil {
    type Output = El;
}

impl<El, N, Stk> ElStack<El> for HCons<ZShift<N>, Stk>
    where
        El : EShift<There<N>>, // NOTE: If we switch to allow shifts of 0, switch to N
        Stk : ElStack<<El as EShift<There<N>>>::Output>,
{
    type Output = <Stk as ElStack<<El as EShift<There<N>>>::Output>>::Output;
}

impl<El, A, Stk> ElStack<El> for HCons<ZApp<A>, Stk> where Stk : ElStack<El> {
    type Output = <Stk as ElStack<El>>::Output;
}

/// Modified version of pure_stack that avoids creating a new kind of stack.
///
/// Consumes a *reversed* stack Self.  This allows the lifts to be consumed in
/// reverse, which means that the Lfts returned by PureStack represent all the
/// Lfts by which the current stack tail would be lifted.  Because the order of
/// conversion during compare_stack doesn't matter, our going in reverse shouldn't
/// be a big problem.  Note that the output Stack is in the same order as the input
/// stack (reversed).
pub trait PureStack<Lfts> {
    type Lfts;
    type Stack;
}

impl<Lfts, N, Stk> PureStack<Lfts> for HCons<ZShift<N>, Stk>
    where
        Lfts : EShift<There<N>>, // NOTE: If we switch to allow shifts of 0, switch to N
        Stk : PureStack<<Lfts as EShift<There<N>>>::Output>,
{
    type Lfts = <Stk as PureStack<<Lfts as EShift<There<N>>>::Output>>::Lfts;
    type Stack = <Stk as PureStack<<Lfts as EShift<There<N>>>::Output>>::Stack;
}

impl<Lfts> PureStack<Lfts> for HNil {
    type Lfts = Lfts;
    type Stack = Self;
}

impl<Lfts, A, Stk> PureStack<Lfts> for HCons<ZApp<A>, Stk> {
    type Lfts = Lfts;
    type Stack = Self;
}

/// Reduction functions

pub trait WhdAll<Ctx> {
    type Output;
}

impl<Term, Ctx> WhdAll<Ctx> for Term
    where
        Ctx : CreateClosInfos<BetaDeltaIota>,
        Term : Inject,
        <Ctx as CreateClosInfos<BetaDeltaIota>>::Info : WhdVal<Term::Output>,
{
    type Output = <<Ctx as CreateClosInfos<BetaDeltaIota>>::Info as WhdVal<Term::Output>>::Output;
}

/// Conversion

/// Conversion utility functions

/// Self is Infos; only needs to deal with pure stack members.
pub trait CompareStacks<Lft1, Stk1, Lft2, Stk2> {
}

/// Empty stacks are equal.
impl<Lft1, Lft2, Info> CompareStacks<Lft1, HNil, Lft2, HNil> for Info {
}

/// App stacks are equal if the terms are convertible.
impl<Lft1, A1, Stk1, Lft2, A2, Stk2, Info> CompareStacks<Lft1, HCons<ZApp<A1>, Stk1>,
                                                         Lft2, HCons<ZApp<A2>, Stk2>> for Info
    where
        Info : CCnv<PbConv, Lft1, Lft2, A1, A2>,
        Stk1 : PureStack<Lft1>,
        Stk2 : PureStack<Lft2>,
        Info : CompareStacks<<Stk1 as PureStack<Lft1>>::Lfts,
                             <Stk1 as PureStack<Lft1>>::Stack,
                             <Stk2 as PureStack<Lft2>>::Lfts,
                             <Stk2 as PureStack<Lft2>>::Stack>,
{
}

/// Convertibility of sorts

pub struct PbConv;

pub struct PbCumul;

/// S0 ~ S1 using conversion strategy Self
pub trait SortCmp<S0, S1> {
    // type Conv;
}

/// Syntactically equal sorts are equal for any conversion strategy.
impl<Pb, S> SortCmp<S, S> for Pb {
    // type Conv = True;
}

/// Set is convertible with Type where conversion is cumulative.
impl SortCmp<Set, Type> for PbCumul {
    // type Conv = True;
}

/* /// Set is not convertible with Type where conversion is exact.
impl SortCmp<Set, Type> for PbConv {
    type Conv = False;
}

/// Type is never convertible with Set.
impl<Pb> SortCmp<Type, Set> for Pb {
    type Conv = False;
} */

/// Conversion between [lft1]term1 and [lft2]term2
pub trait CCnv<CvPb, Lfts1, Lfts2, Term1, Term2> {
    // type Conv;
}

/// Conversion between [lft1](stk1 ⊢ v1) and [lft2](stk2 ⊢ v2)
pub trait EqAppr<CvPb, Lfts1, V1, Stk1, Lfts2, V2, Stk2> {
}

pub trait ConvertStacks<Lft1, Lft2, Stk1, Stk2> {
}

impl<CvPb, Lfts1, Lfts2, Term1, Term2, Info> CCnv<CvPb, Lfts1, Lfts2, Term1, Term2> for Info
    where
        Info : WhdStack<Term1, HNil>,
        Info : WhdStack<Term2, HNil>,
        Info : EqAppr<CvPb, Lfts1, <Info as WhdStack<Term1, HNil>>::Head,
                                   <Info as WhdStack<Term1, HNil>>::Stack,
                            Lfts2, <Info as WhdStack<Term2, HNil>>::Head,
                                   <Info as WhdStack<Term2, HNil>>::Stack>,
{
    // type Conv = Info::Conv;
}

/// Conversion between [lft1](stk1 ⊢ v1 = ref_value_cache fl1', fl1 = FFlex fl1') and
///                    [lft2](stk2 ⊢ v2 = ref_value_cache fl2', fl2 = FFlex fl2')
///
/// (can also be used in general to reduce one side or the other after computation).
pub trait EqApprFlex<CvPb, Lfts1, Fl1, V1, Stk1, Lfts2, Fl2, V2, Stk2> {
    // type Conv;
}

/// Both None : Fl1 and Fl2 must be syntactically equal, and their stacks must be convertible.
impl<CvPb, Lfts1, Fl, Stk1, Lfts2, Stk2, Info>
    EqApprFlex<CvPb, Lfts1, Fl, TNone, Stk1, Lfts2, Fl, TNone, Stk2> for Info
    where
        Info : ConvertStacks<Lfts1, Lfts2, Stk1, Stk2>,
{
    // type Conv = True;
}

/// Fl1 = Some, Fl2 = None : reduce V1 and recompare.
impl<CvPb, Lfts1, Fl1, V1, Stk1, Lfts2, Fl2, Stk2, Info>
    EqApprFlex<CvPb, Lfts1, Fl1, TSome<V1>, Stk1, Lfts2, Fl2, TNone, Stk2> for Info
    where
        Info : WhdStack<V1, Stk1>,
        Info : EqAppr<CvPb, Lfts1, <Info as WhdStack<V1, Stk1>>::Head,
                                   <Info as WhdStack<V1, Stk1>>::Stack,
                            Lfts2, Fl2, Stk2>,
{
}

/// Fl1 = None, Fl2 = Some : reduce V2 and recompare.
impl<CvPb, Lfts1, Fl1, Stk1, Lfts2, Fl2, V2, Stk2, Info>
    EqApprFlex<CvPb, Lfts1, Fl1, TNone, Stk1, Lfts2, Fl2, TSome<V2>, Stk2> for Info
    where
        Info : WhdStack<V2, Stk2>,
        Info : EqAppr<CvPb, Lfts1, Fl1, Stk1,
                            Lfts2, <Info as WhdStack<V2, Stk2>>::Head,
                                   <Info as WhdStack<V2, Stk2>>::Stack>
{
}

/// Both Some : reduce both sides and recompare.
impl<CvPb, Lfts1, Fl1, V1, Stk1, Lfts2, Fl2, V2, Stk2, Info>
    EqApprFlex<CvPb, Lfts1, Fl1, TSome<V1>, Stk1, Lfts2, Fl2, TSome<V2>, Stk2> for Info
    where
        Info : WhdStack<V1, Stk1>,
        Info : WhdStack<V2, Stk2>,
        Info : EqAppr<CvPb, Lfts1, <Info as WhdStack<V1, Stk1>>::Head,
                                   <Info as WhdStack<V1, Stk1>>::Stack,
                            Lfts2, <Info as WhdStack<V2, Stk2>>::Head,
                                   <Info as WhdStack<V2, Stk2>>::Stack>,
{
}

/// NOTE: The pure version of Stk1 and Stk2 is necessarily empty if the term typechecked
impl<CvPb, Lfts1, S1, Stk1, Lfts2, S2, Stk2, Info>
    EqAppr<CvPb, Lfts1, FVal<Sort<S1>>, Stk1, Lfts2, FVal<Sort<S2>>, Stk2> for Info
    where CvPb : SortCmp<S1, S2> {
}

/// Normal rels (which have no associated body) compare equal only if they are equal in this lift
/// environment and their stacks are equal.
impl<CvPb, Lfts1, N1, Stk1, Lfts2, N2, Stk2, Info>
    EqAppr<CvPb, Lfts1, FVal<Rel<N1>>, Stk1, Lfts2, FVal<Rel<N2>>, Stk2> for Info
    where
        Stk1 : ElStack<Lfts1>,
        Stk2 : ElStack<Lfts2>,
        <Stk1 as ElStack<Lfts1>>::Output : RelocRel<N1>,
        <Stk2 as ElStack<Lfts2>>::Output : RelocRel<N2>,
        <<Stk1 as ElStack<Lfts1>>::Output as RelocRel<N1>>::Output :
            Equal<<<Stk2 as ElStack<Lfts2>>::Output as RelocRel<N2>>::Output>,
        Info : ConvertStacks<Lfts1, Lfts2, Stk1, Stk2>,
{
}

/// Flexes compare equal only if they are equal (no lift is needed, since we can evaluate them
/// in the shared environment) and their stacks are equal, or they evaluate to equal terms.
/// The second subsumes the first, so for now we just always reduce both sides, but for
/// efficiency we may want to check the first before the second (we also want to try reducing
/// one side at a time, e.g. the first before the second, according to some oracle order, and
/// then rechecking, in case we get lucky and arrive at a syntactic equality).
impl<CvPb, Lfts1, Fl1, Stk1, Lfts2, Fl2, Stk2, Info>
    EqAppr<CvPb, Lfts1, FFlex<Fl1>, Stk1, Lfts2, FFlex<Fl2>, Stk2> for Info
    where
        Info : RefValueCache<Fl1>,
        Info : RefValueCache<Fl2>,
        Info : EqApprFlex<CvPb, Lfts1, FFlex<Fl1>, <Info as RefValueCache<Fl1>>::Output, Stk1,
                          Lfts2, FFlex<Fl2>, <Info as RefValueCache<Fl2>>::Output, Stk2>,
{
}

/// Lambdas compare equal when their types compare equal and their bodies compare equal in the
/// lifted environment.
///
/// NOTE: Stk1 and Stk2 should actually be *empty* for well-typed terms; we try enforcing it here.
/// This means we don't need to run ElStack on Lfts1 or Lfts2 either.
impl<CvPb, Lfts1, T1, B1, E1, /*Stk1, */Lfts2, T2, B2, E2, /*Stk2, */Info>
    EqAppr<CvPb, Lfts1, FCbn<Lambda<T1, B1>, E1>, /*Stk1*/HNil,
                 Lfts2, FCbn<Lambda<T2, B2>, E2>, /*Stk2*/HNil> for Info
    where
        // Types are convertible (exact conversion)
        T1 : MkClos<E1>,
        T2 : MkClos<E2>,
        Info : CCnv<PbConv, Lfts1, Lfts2, <T1 as MkClos<E1>>::Output, <T2 as MkClos<E2>>::Output>,
        // Bodies are convertible (in lifted environments with exact conversion)
        Lfts1 : ELift,
        Lfts2 : ELift,
        E1 : SubsLift,
        E2 : SubsLift,
        B1 : MkClos<<E1 as SubsLift>::Output>,
        B2 : MkClos<<E2 as SubsLift>::Output>,
        Info : CCnv<PbConv, <Lfts1 as ELift>::Output, <Lfts2 as ELift>::Output,
                            <B1 as MkClos<<E1 as SubsLift>::Output>>::Output,
                            <B2 as MkClos<<E2 as SubsLift>::Output>>::Output>,
{
}

/// Products compare equal when their types compare equal and their bodies compare equal in the
/// lifted environment.
///
/// NOTE: Stk1 and Stk2 should satisfy is_empty for well-typed terms, but it may not actually be
/// empty.  Thus we need to run ElStack on Lfts1 and Lfts2 (also, we might be throwing away some
/// things on the stack?  Should investigate further).
///
/// NOTE: The types of the Cs are converted exactly but the dependent types are converted according
///       to the current strategy.
impl<CvPb, Lfts1, T1, C1, E1, Stk1, Lfts2, T2, C2, E2, Stk2, Info>
    EqAppr<CvPb, Lfts1, FCbn<Prod<T1, C1>, E1>, Stk1,
                 Lfts2, FCbn<Prod<T2, C2>, E2>, Stk2> for Info
    where
        // Extract lifts from stacks.
        Stk1 : ElStack<Lfts1>,
        Stk2 : ElStack<Lfts2>,
        // Types are convertible (exact conversion)
        T1 : MkClos<E1>,
        T2 : MkClos<E2>,
        Info : CCnv<PbConv, <Stk1 as ElStack<Lfts1>>::Output, <Stk2 as ElStack<Lfts2>>::Output,
                            <T1 as MkClos<E1>>::Output, <T2 as MkClos<E2>>::Output>,
        // Bodies are convertible (in lifted environments with current conversion strategy);
        // Luo's system
        <Stk1 as ElStack<Lfts1>>::Output : ELift,
        <Stk2 as ElStack<Lfts2>>::Output : ELift,
        E1 : SubsLift,
        E2 : SubsLift,
        C1 : MkClos<<E1 as SubsLift>::Output>,
        C2 : MkClos<<E2 as SubsLift>::Output>,
        Info : CCnv<CvPb, <<Stk1 as ElStack<Lfts1>>::Output as ELift>::Output,
                          <<Stk2 as ElStack<Lfts2>>::Output as ELift>::Output,
                          <C1 as MkClos<<E1 as SubsLift>::Output>>::Output,
                          <C2 as MkClos<<E2 as SubsLift>::Output>>::Output>,
{
}

/// Macro for generating boilerplate trait impls for EqAppr with FLambda only on the left side.
/// TODO: Find a way to generalize this sort of macro.
macro_rules! impl_eqappr_flambda_lhs {
    ([$($param:ident),*], $constr:ty) => {
        /// Eta-expansion on the fly
        ///
        /// NOTE: Stk1 should be *empty* here for well-typed terms; we try enforcing it here.
        impl<CvPb, Lfts1, T1, B1, E1, Lfts2, $($param, )*Stk2, Info>
            EqAppr<CvPb, Lfts1, FCbn<Lambda<T1, B1>, E1>, HNil, Lfts2, $constr, Stk2> for Info
            where
                // Body of Lambda is convertible with eta expanded non-Lambda term (in lifted
                // environments with exact conversion).
                //
                // NOTE: We don't try to convert the type parameter here, which may or may not lead
                //       to problems down the line.  TODO: see if we can get this to show up in the
                //       Coq kernel.
                Lfts1 : ELift,
                Lfts2 : ELift,
                E1 : SubsLift,
                B1 : MkClos<<E1 as SubsLift>::Output>,
                Stk2 : EtaExpandStack,
                // We call EqApprFlex just to reduce both sides before recursing.
                Info : EqApprFlex<PbConv, <Lfts1 as ELift>::Output, (),
                                          TSome<<B1 as MkClos<<E1 as SubsLift>::Output>>::Output>,
                                          HNil,
                                          <Lfts2 as ELift>::Output, (),
                                          TSome<$constr>, <Stk2 as EtaExpandStack>::Output>,
        {
        }
    }
}

// NOTE: Sorts do not have product types so we should never try to convert them with Lambdas.
// impl_eqappr_flambda_lhs!([S], FVal<Sort<S>>);
impl_eqappr_flambda_lhs!([N], FVal<Rel<N>>);
impl_eqappr_flambda_lhs!([Fl], FFlex<Fl>);
// NOTE: Products do not have product types so we should never try to convert them with Lambdas.
// impl_eqappr_flambda_lhs!([T, C, E], FCbn<Prod<T, C>, E>);

/// Macro for generating boilerplate trait impls for EqAppr with FLambda only on the right side.
/// TODO: Find a way to generalize this sort of macro.
macro_rules! impl_eqappr_flambda_rhs {
    ([$($param:ident),*], $constr:ty) => {
        /// Eta-expansion on the fly
        ///
        /// NOTE: Stk2 should be *empty* here for well-typed terms; we try enforcing it here.
        impl<CvPb, Lfts1, $($param, )*Stk1, Lfts2, T2, B2, E2, Info>
            EqAppr<CvPb, Lfts1, $constr, Stk1, Lfts2, FCbn<Lambda<T2, B2>, E2>, HNil> for Info
            where
                // Body of Lambda is convertible with eta expanded non-Lambda term (in lifted
                // environments with exact conversion).
                //
                // NOTE: We don't try to convert the type parameter here, which may or may not lead
                //       to problems down the line.  TODO: see if we can get this to show up in the
                //       Coq kernel.
                Lfts1 : ELift,
                Lfts2 : ELift,
                E2 : SubsLift,
                B2 : MkClos<<E2 as SubsLift>::Output>,
                Stk1 : EtaExpandStack,
                // We call EqApprFlex just to reduce both sides before recursing.
                Info : EqApprFlex<PbConv, <Lfts1 as ELift>::Output, (),
                                          TSome<$constr>, <Stk1 as EtaExpandStack>::Output,
                                          <Lfts2 as ELift>::Output, (),
                                          TSome<<B2 as MkClos<<E2 as SubsLift>::Output>>::Output>,
                                          HNil>,
        {
        }
    }
}

// NOTE: Sorts do not have product types so we should never try to convert them with Lambdas.
// impl_eqappr_flambda_rhs!([S], FVal<Sort<S>>);
impl_eqappr_flambda_rhs!([N], FVal<Rel<N>>);
impl_eqappr_flambda_rhs!([Fl], FFlex<Fl>);
// NOTE: Products do not have product types so we should never try to convert them with Lambdas.
// impl_eqappr_flambda_rhs!([T, C, E], FCbn<Prod<T, C>, E>);

/// Macro for generating boilerplate trait impls for EqAppr with FFlex only on the left side.
/// TODO: Find a way to generalize this sort of macro.
macro_rules! impl_eqappr_fflex_lhs {
    ([$($param:ident),*], $constr:ty) => {
        impl<CvPb, Lfts1, Fl1, Stk1, Lfts2, $($param, )*Stk2, Info>
            EqAppr<CvPb, Lfts1, FFlex<Fl1>, Stk1, Lfts2, $constr, Stk2> for Info
            where
                Info : RefValueCache<Fl1>,
                Info : EqApprFlex<CvPb,
                                  Lfts1, FFlex<Fl1>, <Info as RefValueCache<Fl1>>::Output, Stk1,
                                  Lfts2, $constr, TNone, Stk2>,
        {
        }
    }
}

impl_eqappr_fflex_lhs!([S], FVal<Sort<S>>);
// NOTE: It seems clear that FFlex cannot ever reduce to a FRel, since each decl in the
// environment should be closed over all previous decls in that environment, but Rel means
// a free variable within the current substitution environment (i.e. a lifted variable)
// which necessarily comes after the decls.
// impl_eqappr_fflex_lhs!([N], FVal<Rel<N>>);
// NOTE: Lambdas come first in Coq's reduction.
// impl_eqappr_fflex_lhs!([T, C, E], FCbn<Lambda<T, C>, E>);
impl_eqappr_fflex_lhs!([T, C, E], FCbn<Prod<T, C>, E>);

/// Macro for generating boilerplate trait impls for EqAppr with FFlex only on the right side.
/// TODO: Find a way to generalize this sort of macro.
macro_rules! impl_eqappr_fflex_rhs {
    ([$($param:ident),*], $constr:ty) => {
        impl<CvPb, Lfts1, $($param, )*Stk1, Lfts2, Fl2, Stk2, Info>
            EqAppr<CvPb, Lfts1, $constr, Stk1, Lfts2, FFlex<Fl2>, Stk2> for Info
            where
                Info : RefValueCache<Fl2>,
                Info : EqApprFlex<CvPb,
                                  Lfts1, $constr, TNone, Stk1,
                                  Lfts2, FFlex<Fl2>, <Info as RefValueCache<Fl2>>::Output, Stk2>,
        {
        }
    }
}

impl_eqappr_fflex_rhs!([S], FVal<Sort<S>>);
// NOTE: It seems clear that FFlex cannot ever reduce to a FRel, since each decl in the
// environment should be closed over all previous decls in that environment, but Rel means
// a free variable within the current substitution environment (i.e. a lifted variable)
// which necessarily comes after the decls.
// impl_eqappr_fflex_rhs!([N], FVal<Rel<N>>);
// NOTE: Lambdas come first in Coq's reduction.
// impl_eqappr_fflex_rhs!([T, C, E], FCbn<Lambda<T, C>, E>);
impl_eqappr_fflex_rhs!([T, C, E], FCbn<Prod<T, C>, E>);

/* /// Temporary conversion hack: exact equality after weak head reduction.
impl<CvPb, Lfts1, V1, Stk1, Lfts2, V2, Stk2, Info>
    EqAppr<CvPb, Lfts1, V1, Stk1, Lfts2, V2, Stk2> for Info
    where
        V1 : Equal<V2>,
        Stk1 : Equal<Stk2>,
{
} */

impl<Lft1, Lft2, Stk1, Stk2, Info> ConvertStacks<Lft1, Lft2, Stk1, Stk2> for Info
    where
        // Reverse stacks to satisfy PureStack precondition
        Stk1 : IntoReverse,
        Stk2 : IntoReverse,
        // Purify both stacks to staisfy CompareStacks precondition
        <Stk1 as IntoReverse>::Output : PureStack<Lft1>,
        <Stk2 as IntoReverse>::Output : PureStack<Lft2>,
        // Compare both stacks.
        Info : CompareStacks<<<Stk1 as IntoReverse>::Output as PureStack<Lft1>>::Lfts,
                             <<Stk1 as IntoReverse>::Output as PureStack<Lft1>>::Stack,
                             <<Stk2 as IntoReverse>::Output as PureStack<Lft2>>::Lfts,
                             <<Stk2 as IntoReverse>::Output as PureStack<Lft2>>::Stack>
{
}

pub trait FConv<CvPb, T1, T2> {
}

impl<CvPb, T1, T2, Ctx> FConv<CvPb, T1, T2> for Ctx
    where
        Ctx : CreateClosInfos<BetaIotaZeta>,
        T1 : Inject,
        T2 : Inject,
        <Ctx as CreateClosInfos<BetaIotaZeta>>::Info : CCnv<CvPb, ElId, ElId, T1::Output, T2::Output>,
{
}

/// Self is the type context.
pub trait ConvLeq<T1, T2>/*: JudgeOfSort*/ {
}

impl<T1, T2, Ctx> ConvLeq<T1, T2> for Ctx
    where
        // T1 : Execute<Ctx, Type = Self>,
        // T2 : Execute<Ctx, Type = Self>,
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

pub trait TypeJudgment {
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<S> TypeJudgment for Sort<S>
    where S : JudgeOfSort,
{
    type Sort = S;

    /* ty.whd_all(self, iter::empty())?; // Mutates in-place.
    match *ty {
        Constr::Sort(ref s) => Ok((self, s)),
        _ => Err(Box::new(CaseError::Type(error_not_type(self, (c.clone(), ty_.clone()))))),
    } */
}

pub trait JudgeOfType {
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl JudgeOfType for Sort<Set> {
    type Sort = Type;
}

pub trait JudgeOfApply<H, HJ, Ctx> {
    type Type;
}

impl<Ctx, H, HJ, T, C> JudgeOfApply<H, HJ, Ctx> for Prod<T, C>
    where
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

pub trait SortOfProduct<T, C>
    where
        /*Sort<T>*/T : JudgeOfSort,
        /*Sort<C>*/C : JudgeOfSort,
{
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<Ctx> SortOfProduct<Type, Type> for Ctx {
    type Sort = Type;
}

impl<Ctx> SortOfProduct<Type, Set> for Ctx {
    type Sort = Type;
}

impl<Ctx> SortOfProduct<Set, Type> for Ctx {
    type Sort = Type;
}

impl<Ctx> SortOfProduct<Set, Set> for Ctx {
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

pub trait Execute<Ctx> {
    type Type : /*JudgeOfSort + *//*?Sized*/;// : JudgeOfSort<Ctx> + ?Sized;
}

impl<S, Ctx> Execute<Ctx> for Sort<S>
    where
        Self : JudgeOfType,
        // Ctx : Execute<Ty::Unlift, Output=Set>,
        // Ctx::Subs : AtIndex</*::Unlifted*/Index>,
        // <Ctx::Subs as AtIndex<Index>>::Output: RDecl,
        // <<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type : Lift<Index>,
        // <<<Ctx::Subs as AtIndex<Index>>::Output as RDecl>::Type as Lift<Index>>::Output : JudgeOfSort<Ctx>
        // Ty : UnLift<Index>,
{
    type Type = Sort<<Self as JudgeOfType>::Sort>;
}

impl<Index, Ctx : Context> Execute<Ctx> for Rel<Index>
    where
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
        // Ctx : DecomposeApp<F, HCons<A, HNil>>,
        A : Execute<Ctx>,
        F : Execute<Ctx>,
        F::Type : WhdAll<Ctx>,
        <F::Type as WhdAll<Ctx>>::Output : JudgeOfApply<A, A::Type, Ctx>,
        // <Term::Type as WhdAll<Ctx>>::Output : TypeJudgment,
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

impl<T, C, Ctx : Context> Execute<Ctx> for Lambda<T, C>
    where
        T : ExecuteType<Ctx>,
        C : Execute<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>,
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

impl<T, C, Ctx : Context> Execute<Ctx> for Prod<T, C>
    where
        T : ExecuteType<Ctx>,
        C : ExecuteType<HCons<Assum<T>, /*<Ctx as Generic*/<Ctx as RawContext>::Subs/*>::Repr*/>>,
        Ctx : SortOfProduct<<T as ExecuteType<Ctx>>::Sort,
                            <C as ExecuteType<HCons<Assum<T>, <Ctx as RawContext>::Subs>>>::Sort>,
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

pub trait ExecuteType<Ctx>
    // Self: Execute<Ctx>,
    // Self::Type : JudgeOfSort/*<Ctx>*/,
{
    type Sort /*where Sort<Self::Sort>*/ : JudgeOfSort;
}

impl<Term, Ctx> ExecuteType<Ctx> for Term
    where
        Term : Execute<Ctx>,
        Term::Type : WhdAll<Ctx>,
        <Term::Type as WhdAll<Ctx>>::Output : TypeJudgment,
        /*Term : Execute<Ctx>,
        Term::Type : JudgeOfSort/*<Ctx>*/,*/
{
    type Sort = <<Term::Type as WhdAll<Ctx>>::Output as TypeJudgment>::Sort;//<Term::Type as JudgeOfSort>::Sort;
}

#[cfg(test)]
mod test {
    use frunk::hlist::{HCons, HNil, LiftFrom, Selector};
    use frunk::indices::{Here, There};
    use super::*;

    #[derive(Generic, LabelledGeneric)]
    struct MyContext<Subs> {
        subs: Subs,
    }

    impl<Subs> RawContext for MyContext<Subs> {
        type Subs = Subs;
    }

    impl<Subs> MyContext<Subs> {
        fn my_judge_sort<Ty, S>(/*, x : X*/)
            where
                Ty : ExecuteType<Self, Sort = S>,
                S : JudgeOfSort,
                //Ty : ExecuteType<Self>,
                //Ty: TypeJudgment,
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

        fn my_whd<E, V>()
            where
                E : Execute<Self>,
                E::Type : ExecuteType<Self>,
                E : WhdAll<Self, Output = V>,
        {
        }

        fn my_conv<E1, E2>()
            where
                E1 : Execute<Self>,
                E2 : Execute<Self>,
                // E1::Type : ExecuteType<Self>,
                // E2::Type : ExecuteType<Self>,
                Self : ConvLeq<E1::Type, E2::Type>,
                Self : ConvLeq<E1, E2>,
        {
        }

        fn my_conv_sort<E1, E2>()
            where
                // E1 : Execute<Self>,
                // E2 : Execute<Self>,
                // E1::Type : ExecuteType<Self>,
                // E2::Type : ExecuteType<Self>,
                // Self : ConvLeq<E1::Type, E2::Type>,
                Self : ConvLeq<E1, E2>,
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
        Ctx::my_judge_sort::<Prod<Sort<Set>, Sort<Set>>, Type>();
        Ctx::my_judge_sort::<Prod<Rel<There<Here>>, Sort<Set>>, Type>();
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
        // Note: below test is basically a duplicate
        MyContext::<Hlist![Assum<Rel<Here>>, Assum<Sort<Set>>]>::
            my_judge_type::<App<Lambda<Sort<Set>, Lambda<Rel<Here>, Rel<Here>>>, Rel<There<Here>>>,
                            Prod<Rel<There<Here>>, Rel<There<There<Here>>>>,
                            Set>();
        MyContext::<Hlist![Assum<Rel<Here>>, Assum<Sort<Set>>]>::
            my_judge_type::<App<App<Lambda<Sort<Set>, Lambda<Rel<Here>, Rel<Here>>>, Rel<There<Here>>>, Rel<Here>>,
                            Rel<There<Here>>,
                            Set>();
        MyContext::<Hlist![Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<App<Lambda<Sort<Set>, Rel<Here>>, Rel<Here>>, Rel<Here>>,
                            Prod<App<Lambda<Sort<Set>, Rel<Here>>, Rel<Here>>, App<Lambda<Sort<Set>, Rel<Here>>, Rel<There<Here>>>>,
                            Set>();
        MyContext::<Hlist![Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<App<Lambda<Sort<Set>, Rel<Here>>, Rel<Here>>,
                                   App<Lambda<App<Lambda<Sort<Set>, Rel<Here>>,
                                                  Rel<There<Here>>>,
                                              Rel<Here>>,
                                       Rel<Here>>>,
                            Prod<App<Lambda<Sort<Set>, Rel<Here>>, Rel<Here>>, App<Lambda<Sort<Set>, Rel<Here>>, Rel<There<Here>>>>,
                            Set>();
        /*MyContext::<Hlist![Decl<App<Lambda<Sort<Type>, Rel<Here>>, Sort<Set>>, Sort<Type>>]>::
            my_judge_type::<Rel<Here>, /*Sort<Set>*/Rel<There<Here>>, Type>();*/
        MyContext::<Hlist![Assum<Rel<Here>>, Decl<App<Lambda<Sort<Type>, Rel<Here>>, Sort<Set>>, Sort<Type>>]>::
            my_judge_type::<Rel<Here>, /*Sort<Set>*/Rel<There<Here>>, Type>();
        Ctx::my_judge_type::<Lambda<Sort<Set>,
                                    Lambda<Prod<Sort<Set>, Rel<There<Here>>>,
                                           App<Rel<Here>, Rel<There<Here>>>>>,
                             Prod<Sort<Set>,
                                  Prod<Prod<Sort<Set>, Rel<There<Here>>>,
                                       Rel<There<Here>>>>,
                             Type>();
        Ctx::my_judge_type::<Lambda<Sort<Set>,
                                    Lambda<Prod<Sort<Set>, Rel<Here>>,
                                           App<Rel<Here>, Rel<There<Here>>>>>,
                             Prod<Sort<Set>,
                                  Prod<Prod<Sort<Set>, Rel<Here>>,
                                       Rel<There<Here>>>>,
                             Type>();
        // Below should error: would require a universe larger than Type.
        // Ctx::my_judge_type::<Prod<Sort<Type>, Rel<There<Here>>>, Sort<Type>, _>();
        // Below requires weak head reduction to be at least partially implemented (for rels) in order to succeed.
        MyContext::<Hlist![Assum<Rel<Here>>, Decl<Sort<Set>, Sort<Type>>]>::
            my_judge_sort::<Rel<Here>, Set>();
        MyContext::<Hlist![Decl<Lambda<Rel<There<Here>>, Rel<Here>>, Prod<Rel<There<Here>>, Rel<There<There<Here>>>>>, Assum<Rel<Here>>, Decl<Sort<Set>, Sort<Type>>]>::
            my_judge_sort::<App<Rel<Here>, Rel<There<Here>>>, Set>();
        MyContext::<Hlist![Decl<Prod<Sort<Set>, Sort<Set>>,
                                Sort<Type>>,
                           Assum<Sort<Set>>]>::
            my_judge_sort::<App<Lambda<Sort<Set>, Prod<Rel<There<Here>>, Rel<There<There<Here>>>>>, Rel<There<Here>>>, Type>();
        MyContext::<Hlist![Assum<Rel<Here>>, Assum<Sort<Set>>]>::
            my_whd::<App<Lambda<Sort<Set>, Rel<Here>>, Rel<There<Here>>>, Rel<There<Here>>>();
        // Below requires conversion to be at least partially implemented in order to succeed.
        MyContext::<Hlist![Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Rel<Here>,
                                   App<Lambda<App<Lambda<Sort<Set>, Rel<Here>>,
                                                  Rel<There<Here>>>,
                                              Rel<Here>>,
                                       Rel<Here>>>,
                            Prod<Rel<Here>, App<Lambda<Sort<Set>, Rel<Here>>, Rel<There<Here>>>>,
                            Set>();
        // Below (probably) requires conversion to be implemented for Flex (assuming betaiotazeta
        // is used during conversion).
        //
        // X : Set, Y := X ⊢ λ x : X . (λ y : (λ Z : Set . Z) Y . y) x : X → (λ Z : Set . Z) Y
        MyContext::<Hlist![Decl<Rel<Here>, Sort<Set>>, Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Rel<There<Here>>,
                                   App<Lambda<App<Lambda<Sort<Set>, Rel<Here>>,
                                                  Rel<There<Here>>>,
                                              Rel<Here>>,
                                       Rel<Here>>>,
                            Prod<Rel<There<Here>>, App<Lambda<Sort<Set>, Rel<Here>>, Rel<There<Here>>>>,
                            Set>();
        MyContext::<Hlist![Assum<Sort<Set>>]>::
            my_judge_sort::<Prod<Prod<Rel<Here>, Rel<There<Here>>>, Rel<There<Here>>>, _>();
        MyContext::<Hlist![Assum<Sort<Set>>]>::
            my_judge_sort::<Prod<Prod<Rel<Here>, Rel<There<Here>>>, Sort<Set>>, Type>();
        // Requires conversion to be implemented for rels.
        MyContext::<Hlist![Assum<Sort<Set>>]>::
            my_conv::<Lambda<Sort<Set>, Rel<Here>>, App<Lambda<Sort<Set>, Lambda<Sort<Set>, Rel<Here>>>, Rel<Here>>>();
        // Requires conversion to be implemented for app stacks.
        MyContext::<Hlist![Assum<Prod<Rel<Here>, Sort<Set>>>, Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Prod<Rel<There<Here>>,
                                        App<Rel<There<Here>>, Rel<Here>>>,
                            Lambda<Rel<There<There<Here>>>,
                                   App<Lambda<App<Rel<There<There<Here>>>,
                                                  Rel<Here>>,
                                              Rel<Here>>,
                                       App<Rel<There<Here>>,
                                           App<Lambda<Rel<There<There<There<Here>>>>, Rel<Here>>,
                                               Rel<Here>>
                                          >
                                      >
                                  >>,
                            _,
                            _>();
        // X : Set, Y : (X → X) → Set ⊢
        //  λ f : (∀ x : X → X . Y x) .
        //      (λ y : (Y (λ (z : X) . z)) . y)
        //      (f (λ z : X . (λ (w : X) . w) z))
        // Requires conversion to be implemented for lambdas and app stacks.
        MyContext::<Hlist![Assum<Prod<Prod<Rel<Here>, Rel<There<Here>>>, Sort<Set>>>, Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Prod<Prod<Rel<There<Here>>, Rel<There<There<Here>>>>,
                                        App<Rel<There<Here>>, Rel<Here>>>,
                                   App<Lambda<App<Rel<There<Here>>,
                                                  Lambda<Rel<There<There<Here>>>,
                                                         Rel<Here>>>,
                                              Rel<Here>>,
                                       App<Rel<Here>,
                                           Lambda<Rel<There<There<Here>>>,
                                                  App<Lambda<Rel<There<There<There<Here>>>>, Rel<Here>>,
                                                      Rel<Here>>>
                                          >
                                      >
                                  >,
                            _,
                            _>();
        // Requires conversion to be implemented for Set : Type, and flex on lhs.
        // (Note: not sure whether we can actually trigger this conversion with just one universe?)
        MyContext::<Hlist![Decl<Sort<Set>, Sort<Type>>]>::
            my_conv_sort::<Rel<Here>, Sort<Type>>();
        // Requires conversion to be implemented for prod, and flex on rhs.
        MyContext::<Hlist![Decl<Prod<Sort<Set>, Sort<Set>>,
                                Sort<Type>>,
                           Assum<Sort<Set>>]>::
            my_conv::<Prod<App<Lambda<Sort<Set>, Sort<Set>>, Rel<There<Here>>>, Sort<Set>>,
                      Rel<Here>>();
        // Requires conversion to be implemented for lambdas on lhs (eta expansion)
        // X : Set, Y : ((X → X) → X → X) → Set ⊢
        //  λ f : (∀ x : (X → X) → X → X . Y x) .
        //      (λ y : (Y (λ (z : X → X) . z)) . y)
        //      (f (λ z : X → X . (λ (w : X) . z w)))
        MyContext::<Hlist![Assum<Prod<Prod<Prod<Rel<Here>, Rel<There<Here>>>,
                                           Prod<Rel<There<Here>>, Rel<There<There<Here>>>>>,
                                      Sort<Set>>>,
                           Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Prod<Prod<Prod<Rel<There<Here>>, Rel<There<There<Here>>>>,
                                             Prod<Rel<There<There<Here>>>,
                                                  Rel<There<There<There<Here>>>>>>,
                                        App<Rel<There<Here>>, Rel<Here>>>,
                                   App<Lambda<App<Rel<There<Here>>,
                                                  Lambda<Prod<Rel<There<There<Here>>>,
                                                              Rel<There<There<There<Here>>>>>,
                                                         Rel<Here>>>,
                                              Rel<Here>>,
                                       App<Rel<Here>,
                                           Lambda<Prod<Rel<There<There<Here>>>,
                                                       Rel<There<There<There<Here>>>>>,
                                                  Lambda<Rel<There<There<There<Here>>>>,
                                                         App<Rel<There<Here>>, Rel<Here>>>>
                                          >
                                      >
                                  >,
                            _,
                            _>();
        // Requires conversion to be implemented for lambdas on rhs (eta expansion)
        // X : Set, Y : ((X → X) → X → X) → Set ⊢
        //  λ f : (∀ x : (X → X) → X → X . Y x) .
        //      (λ y : (Y (λ (z : X → X) . z)) . y)
        //      (f (λ z : X → X . (λ (w : X) . z w)))
        MyContext::<Hlist![Assum<Prod<Prod<Prod<Rel<Here>, Rel<There<Here>>>,
                                           Prod<Rel<There<Here>>, Rel<There<There<Here>>>>>,
                                      Sort<Set>>>,
                           Assum<Sort<Set>>]>::
            my_judge_type::<Lambda<Prod<Prod<Prod<Rel<There<Here>>, Rel<There<There<Here>>>>,
                                             Prod<Rel<There<There<Here>>>,
                                                  Rel<There<There<There<Here>>>>>>,
                                        App<Rel<There<Here>>, Rel<Here>>>,
                                   App<Lambda<App<Rel<There<Here>>,
                                                  Lambda<Prod<Rel<There<There<Here>>>,
                                                              Rel<There<There<There<Here>>>>>,
                                                         Lambda<Rel<There<There<There<Here>>>>,
                                                                App<Rel<There<Here>>, Rel<Here>>>>>,
                                              Rel<Here>>,
                                       App<Rel<Here>,
                                           Lambda<Prod<Rel<There<There<Here>>>,
                                                       Rel<There<There<There<Here>>>>>,
                                                  Rel<Here>>
                                          >
                                      >
                                  >,
                            _,
                            _>();
        /* // Correctly fails (not convertible):
        MyContext::<Hlist![Decl<Prod<Sort<Set>, Sort<Set>>,
                                Sort<Type>>,
                           Assum<Sort<Set>>]>::
            my_conv::<Rel<Here>,
                      Prod<App<Lambda<Sort<Set>, Prod<Rel<There<Here>>, Rel<There<There<Here>>>>>, Rel<There<Here>>>, Sort<Set>>>(); */
    }
}
