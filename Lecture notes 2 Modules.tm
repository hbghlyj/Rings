<TeXmacs|2.1.2>

<style|<tuple|article|number-long-article>>

<\body>
  <\hide-preamble>
    <new-remark|observation|Observation>

    <assign|remark-name|<\macro|name>
      <em|<arg|name>>
    </macro>>

    <assign|example-text|<macro|<inactive|<localize|Example>>>>

    <assign|example|<\macro|body>
      <surround|<compound|next-example>||<compound|render-theorem|<compound|example-numbered|<compound|example-text>|<compound|the-example>>|<arg|body>>>
    </macro>>

    <assign|render-theorem|<\macro|which|body>
      <render-enunciation|<theorem-name|<arg|which><theorem-sep>>|<arg|body>>
    </macro>>
  </hide-preamble>

  <inc-section><inc-section><inc-section><section|Modules: an introduction>

  Suppose that <math|R> is a ring and <math|M> is a commutative group with
  operation +. A map <math|.\<#2236\>R\<times\>M\<rightarrow\>M;(r,x)\<mapsto\>r.x>
  is called a <strong|scalar multiplication of <math|R> on <math|M>> if

  <no-indent>(M1) <math|1.x=x> for all <math|x\<in\>M>;

  <no-indent>(M2) <math|r.(s.x)=(r*s).x> for all <math|r,s\<in\>R> and
  <math|x\<in\>M>;

  <no-indent>(M3) <math|(r+s).x=(r.x)+(s.x)> for all <math|r,s\<in\>R> and
  <math|x\<in\>M>;

  <no-indent>(M4) <math|r.(x+y)=(r.x)+(r.y)> for all <math|r\<in\>R> and
  <math|x,y\<in\>M>.

  An <strong|<math|R>-module> is a commutative group <math|M>, called the
  <strong|additive group> of the module and whose operation is called
  <strong|addition>, equipped with a scalar multiplication of <math|R> on
  <math|M>. We often speak of simply the module <math|M> if all other data is
  clear, and in this case <math|R> is the <strong|ring of scalars> of
  <math|M>.

  T<with|font-base-size|11|>he elements of <math|M> are called
  <strong|vectors> and the elements of <math|R> are called <strong|scalars>.
  The identity of <math|M> is called the <strong|zero> of the module and
  denoted 0, and for each <math|x\<in\>M> we write <math|\<minus\>x> for the
  unique inverse of <math|x>; the map <math|M\<rightarrow\>M;x\<mapsto\>\<minus\>x>
  is the <strong|negation> of the module.

  <\remark>
    Since <math|M> is a commutative group,
    <math|\<minus\>0=0,\<minus\>(\<minus\>x)=x> for all <math|x\<in\>M>, and
    negation is a homomorphism.

    (M4) says exactly that for <math|r\<in\>R> the map
    <math|M\<rightarrow\>M;x\<mapsto\>r.x> is a group homomorphism of the
    additive group of <math|M>, so <math|r.0<rsub|M>=0<rsub|M>> and
    <math|r.(\<minus\>x)=\<minus\>(r.x)> for all <math|x\<in\>M>.

    (M3) says exactly that for <math|x\<in\>M> the map
    <math|R\<rightarrow\>M;r\<mapsto\>r.x> is a group homomorphism from the
    additive group of <math|R> to the additive group of <math|M>, so
    <math|0<rsub|R>.x=0<rsub|M>> and <math|(\<minus\>r).x=\<minus\>(r.x)> for
    all <math|r\<in\>R>.
  </remark>

  <\example>
    <dueto|Vector spaces as modules>Given a field <math|\<bbb-F\>>, a vector
    space <math|V> is exactly an <math|\<bbb-F\>>-module, with the two
    notions of scalar multiplication coinciding.
  </example>

  <\example>
    <dueto|The zero <math|R>-module>For a ring <math|R>, the trivial group \U
    usually denoted {0} in this context \U and the scalar multiplication
    defined by <math|r.0\<assign\>0> for all <math|r\<in\>R> is a module
    called <strong|the zero <math|R>-module>.

    <with|font|Segoe UI Emoji|\<#26A0\>>If <math|R> is trivial this is the
    <em|only> <math|R>-module, since <math|x=1.x=(1+1).x=1.x+1.x=x+x>, so
    <math|x=0> for all <math|x\<in\>M>.
  </example>

  <\example>
    <dueto|The <math|R>-module <math|R>>For a ring <math|R>, the
    multiplication map on <math|R> is also a scalar multiplication of the
    ring <math|R> on the additive group of <math|R> making <math|R> into an
    <math|R>-module which we call <strong|the <math|R>-module <math|R>>.

    (M1) is exactly the statement that <math|1<rsub|R>> is a left identity of
    ring multiplication; (M2) is exactly associativity of ring
    multiplication; (M3) is exactly that all right multiplication maps on a
    ring are homomorphisms of the additive group; and (M4) is exactly that
    all left multiplication maps on a ring are homomorphisms.

    <with|font|Segoe UI Emoji|\<#26A0\>>There may be more than one scalar
    multiplication of the ring <math|R> on the additive group of <math|R>: we
    saw in Example 1.26 that <math|\<lambda\>.z\<assign\>\<lambda\>z> and
    <math|\<lambda\>.z\<assign\><wide|\<lambda\>|\<wide-bar\>>.z> are two
    different scalar multiplications of <math|\<bbb-C\>> on <math|\<bbb-C\>>.
  </example>

  <\example>
    <dueto|Direct sums>Given <math|R>-modules
    <math|M<rsub|1>,\<ldots\>,M<rsub|n>>, the product group
    <math|M<rsub|1>\<times\>\<cdots\>\<times\>M<rsub|n>> equipped with the
    map <math|(r,x)\<mapsto\>(r<rsub|1>.x<rsub|1>,\<ldots\>,r<rsub|n>.x<rsub|n>)>
    where the <math|i>th instance of . is the scalar multiplication in
    <math|M<rsub|i>>, is a scalar multiplication of <math|R> on
    <math|M<rsub|1>\<times\>\<cdots\>\<times\>M<rsub|n>>. This module is
    denoted <math|M<rsub|1>\<varoplus\>\<cdots\>\<varoplus\>M<rsub|n>> and is
    called the <strong|direct sum> of the <math|R>-modules
    <math|M<rsub|1>,\<ldots\>,M<rsub|n>>.

    In particular the direct sum of <math|n> copies of the <math|R>-module
    <math|R> is called <strong|the <math|R>-module <math|R<rsup|n>>> and the
    scalar multiplication is given by <math|r.x=(r*x<rsub|1>,\<ldots\>,r*x<rsub|n>)>.

    For a field <math|\<bbb-F\>> the <math|\<bbb-F\>>-module
    <math|\<bbb-F\><rsup|n>> is the usual vector space
    <math|\<bbb-F\><rsup|n>>.
  </example>

  <\example>
    <dueto|The <math|M<rsub|n>(R)>-module
    <math|R<rsup|n><rsub|<text|<math|col>>>>>For a ring <math|R>, we write
    <math|R<rsup|n><rsub|<text|col>>> for <math|M<rsub|n,1>(R)>. By
    Proposition 1.44, this is a commutative group and the map
    <math|M<rsub|n>(R)\<times\>R<rsup|n><rsub|<text|<math|col>>>\<rightarrow\>R<rsup|n><rsub|<text|col>>;(A,v)\<mapsto\>A*v>
    is a scalar multiplication of the ring <math|M<rsub|n>(R)> on
    <math|R<rsup|n><rsub|<text|col>>>. We call this <strong|the
    <math|M<rsub|n>(R)>-module <math|R<rsup|n><rsub|<text|<math|col>>>>>.
  </example>

  <\example>
    <dueto|The <math|R>-module <math|R<rsup|n><rsub|<text|col>>>>For a ring
    <math|R>, the additive group <math|R<rsup|n><rsub|<text|<math|col>>>> has
    the structure of an <math|R>-module called <strong|the <math|R>-module
    <math|R<rsup|n><rsub|<text|<math|col>>>>> with scalar multiplication

    <\equation*>
      r\<cdot\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|1|1|cell-rborder|0ln>|<table|<row|<cell|x<rsub|1>>>|<row|<cell|\<vdots\>>>|<row|<cell|x<rsub|n>>>>>>|)>=<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|3|3|cell-rborder|0ln>|<table|<row|<cell|r>|<cell|>|<cell|0>>|<row|<cell|>|<cell|\<ddots\>>|<cell|>>|<row|<cell|0>|<cell|>|<cell|r>>>>>|)><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|1|1|cell-rborder|0ln>|<table|<row|<cell|x<rsub|1>>>|<row|<cell|\<vdots\>>>|<row|<cell|x<rsub|n>>>>>>|)>=<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|1|1|cell-rborder|0ln>|<table|<row|<cell|r*x<rsub|1>>>|<row|<cell|\<vdots\>>>|<row|<cell|r*x<rsub|n>>>>>>|)><space|1em><text|for
      >r\<in\>R,x\<in\>R<rsub|<math-up|col>><rsup|n>
    </equation*>

    For a field <math|\<bbb-F\>> the <math|\<bbb-F\>>-module
    <math|\<bbb-F\><rsup|n><rsub|<text|<math|col>>>> is the usual
    <math|\<bbb-F\>>-vector space <math|\<bbb-F\><rsup|n><rsub|<text|<math|col>>>>.
  </example>

  <\example>
    <dueto|The <math|R>-module <math|M<rsub|n>(R)>>For a ring <math|R>, the
    additive group <math|M<rsub|n>(R)> has the structure of an
    <math|R>-module called <strong|the <math|R>-module <math|M<rsub|n>(R)>>
    with scalar multiplication <math|(r.A)<rsub|i,j>\<assign\>r*A<rsub|i,j>>
    for all <math|1\<leqslant\>i, j\<leqslant\>n>.

    For fields this is the vector space structure described in Example 1.48.
  </example>

  <\example>
    <dueto|The <math|\<bbb-Z\>>-module of a commutative group>Given a
    commutative group <math|M>, the map <math|\<bbb-Z\>\<times\>M\<rightarrow\>M>
    defined by

    <\equation*>
      (n\<minus\>m).x\<assign\><wide|(x+\<cdots\>+x)|\<wide-overbrace\>><rsup|n<text|
      times>>\<minus\><wide|(x+\<cdots\>+x)|\<wide-overbrace\>><rsup|m<text|
      times>>
    </equation*>

    is a scalar multiplication of <math|\<bbb-Z\>> on <math|M> giving it the
    structure of a <math|\<bbb-Z\>>-module called <strong|the
    <math|\<bbb-Z\>>-module <math|M>>. It is the unique
    <math|\<bbb-Z\>>-module on <math|M>.
  </example>

  <\example>
    <dueto|Polynomial rings as <math|R>-modules>The additive group of the
    ring <math|R[X]> can be made into an <math|R[X]>-module \U for example
    the <math|R[X]>-module <math|R[X]> \U but it can also be made into an
    <math|R>-module with scalar multiplication <math|r.(a<rsub|0>+a<rsub|1>X
    +\<cdots\>+a<rsub|n>X<rsub|n>)=(r*a<rsub|0>)+(r*a<rsub|1>)X+\<cdots\>+(r*a<rsub|n>)X<rsup|n>>.
  </example>

  <\example>
    <dueto|Modules over matrix rings as vector spaces>An
    <math|M<rsub|n>(\<bbb-F\>)>-module <math|M> is also vector space over
    <math|\<bbb-F\>> with scalar multiplication

    <\equation*>
      \<lambda\>.v\<assign\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|3|3|cell-rborder|0ln>|<table|<row|<cell|\<lambda\>>|<cell|>|<cell|0>>|<row|<cell|>|<cell|\<ddots\>>|<cell|>>|<row|<cell|0>|<cell|>|<cell|\<lambda\>>>>>>|)>.v<space|1em><text|for
      >\<lambda\>\<in\>\<bbb-F\>,v\<in\>M<rsub|n><around*|(|\<bbb-F\>|)>
    </equation*>
  </example>

  <\example>
    <dueto|Vector spaces with an endomorphism>For
    <math|T\<#2236\>V\<rightarrow\>V> an <math|\<bbb-F\>>-linear map we can
    define a scalar multiplication of <math|\<bbb-F\><around*|[|X|]>> on the
    additive group of <math|V> by

    <\equation*>
      (a<rsub|0>+a<rsub|1>X+\<cdots\>+a<rsub|d>X<rsup|d>).v\<#2236\>=a<rsub|0>.v+a<rsub|1>.T(v)+\<cdots\>+a<rsub|d>.T<rsup|d>(v)<text|
      for all >p\<in\>\<bbb-F\>[X]<text| and >v\<in\>V
    </equation*>

    where the . on the right is the scalar multiplication of <math|\<bbb-F\>>
    on <math|V> resulting from the given vector space structure.
  </example>

  <subsection|Linear maps>

  As with rings we shall be interested in the structure-preserving maps for
  modules: An <strong|<math|R>-linear map> between two <math|R>-modules
  <math|M> and <math|N> is a group homomorphism
  <math|\<phi\>\<#2236\>M\<rightarrow\>N> with
  <math|\<phi\>(r.x)=r.\<phi\>(x)> for all <math|x\<in\>M> and
  <math|r\<in\>R>.

  <\remark>
    Since an <math|R>-linear map <math|\<phi\>\<#2236\>M\<rightarrow\>N> is a
    group homomorphism, <math|\<phi\>(0<rsub|M>)=0<rsub|N>> and
    <math|\<phi\>(\<minus\>x)=\<minus\>\<phi\>(x)> for all <math|x\<in\>M>.
  </remark>

  <\example>
    <dueto|Example 4.2, contd.>For vector spaces <math|V> and <math|W> over a
    field <math|\<bbb-F\>>, the linear maps <math|V\<rightarrow\>W> in the
    usual sense are exactly the <math|\<bbb-F\>>-linear maps in the sense
    defined here.
  </example>

  <\example>
    For an <math|R>-module <math|M> and elements
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>M>, the map
    <math|\<Phi\><rsub|x>\<#2236\>R<rsup|n>\<rightarrow\>M;r\<mapsto\>r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>>
    is <math|R>-linear by (M2) and (M3).
  </example>

  <\example>
    For <math|A\<in\>M<rsub|n,m>(R)> the map
    <math|R<rsup|n>\<rightarrow\>R<rsup|m>;v\<mapsto\>v*A> between the
    <math|R>-modules <math|R<rsup|n>> and <math|R<rsup|m>> is an
    <math|R>-linear map between the <math|R>-modules <math|R<rsup|n>> and
    <math|R<rsup|m>> since <math|r.(v*A)=r(v*A)=(r*v)A=(r.v)A> for all
    <math|r\<in\>R> and <math|v\<in\>R<rsup|n>>, and <math|(v+w)A=v*A+w*A>
    for all <math|v,w\<in\>R<rsup|n>> by Proposition 1.44.
  </example>

  <\example>
    For <math|A\<in\>M<rsub|n,m>(R)> the map
    <math|R<rsup|m><rsub|<text|col>>\<rightarrow\>R<rsup|n><rsub|<text|col>>;v\<mapsto\>A*v>
    between the <math|R>-modules <math|R<rsup|m><rsub|<text|col>>> and
    <math|R<rsup|n><rsub|<text|col>>> is additive since <math|A(v+w)=A*v+A*w>
    by Proposition 1.44.

    If <math|R> is commutative then (writing <math|\<#2206\>(r)> for the
    matrix with <math|r>s on the diagonal and 0 elsewhere as in Example 1.48)
    we have <math|\<#2206\>(r)> is in the centre of the ring
    <math|M<rsub|n>(R)> and so <math|A(r.v)=A(\<#2206\>(r)v)=(A\<#2206\>(r))v=(\<#2206\>(r)A)v=\<#2206\>(r)(A*v)=r.(A*v)>.
    Hence the map <math|R<rsup|m><rsub|<text|col>>\<rightarrow\>R<rsup|n><rsub|<text|col>>;v\<mapsto\>A*v>
    is <math|R>-linear.

    If <math|R> is a non-commutative ring then there are elements
    <math|r,s\<in\>R> with <math|r*s\<neq\>s*r> and the map
    <math|R<rsup|1><rsub|<text|col>>\<rightarrow\>R<rsup|1><rsub|<text|col>>;x\<mapsto\>r*x>
    is <em|not> linear since <math|r(s.1)=r*s\<neq\>s*r=s.(r1)>.
  </example>

  <\example>
    For <math|M> an <math|R>-module and <math|x\<in\>M>, the map
    <math|\<phi\>\<#2236\>R\<rightarrow\>M;r\<mapsto\>r.x> from the
    <math|R>-module <math|R> to <math|M> is <math|R>-linear since
    <math|(r+s).x=(r.x)+(s.x)> by (M3) for <math|M>, and
    <math|(s.r).x=(s*r).x=s.(r.x)> for all <math|r,s\<in\>R> by definition of
    scalar multiplication in the <math|R>-module <math|R> and (M2) for
    <math|M>.
  </example>

  <\example>
    If <math|R> is commutative then the scalar multiplication map
    <math|M\<rightarrow\>M;x\<mapsto\>s.x> is <math|R>-linear since
    <math|s.(r.x)=(s*r).x=(r*s).x=r.(s.x)> for all <math|r\<in\>R> and
    <math|x\<in\>M>.

    On the other hand, for any ring <math|R> if <math|M> is the zero-module
    then the map <math|M\<rightarrow\>M;x\<mapsto\>s.x> is <math|R>-linear.
  </example>

  <\proposition>
    <dueto|Algebra of linear maps>Suppose that <math|M> and <math|N> are
    <math|R>-modules. Then <math|L(M,N)>, the set of <math|R>-linear maps
    <math|M\<rightarrow\>N>, is a subgroup of <math|Hom(M,N)> (under
    pointwise addition). Furthermore, if <math|\<phi\>\<in\>L(M,N)> and
    <math|\<psi\>\<in\>L(N,P)> then <math|\<psi\>\<circ\>\<phi\>\<in\>L(M,P)>,
    and <math|L(M,M)> is a subring of <math|Hom(M,M)>.
  </proposition>

  <\proof>
    Certainly <math|L(M,N)> is a subset of <math|Hom(M,N)>, and the zero map
    <math|z\<#2236\>M\<rightarrow\>N;x\<mapsto\>0<rsub|N>> is a homomorphism,
    and linear since <math|z(r.x)=0<rsub|N>=r.0<rsub|N>=r.z(x)> and so
    <math|L(M,N)> is non-empty. If <math|\<phi\>,\<psi\>\<in\>L(M,N)> then
    <math|\<phi\>\<minus\>\<psi\>> is a homomorphism since <math|Hom(M,N)> is
    a group, and <math|(\<phi\>\<minus\>\<psi\>)(r.x)=\<phi\>(r.x)\<minus\>\<psi\>(r.x)=r.\<phi\>(x)\<minus\>r.\<phi\>(x)=r.(\<phi\>(x)\<minus\>\<psi\>(x))=r.((\<phi\>\<minus\>\<psi\>)(x))>
    so <math|\<phi\>\<minus\>\<psi\>\<in\>L(M,N)> and hence <math|L(M,N)> is
    a subgroup by the subgroup test.

    For the second part, <math|\<psi\>\<circ\>\<phi\>> is a group
    homomorphism, and it is <math|R>-linear since
    <math|(\<psi\>\<circ\>\<phi\>)(r.x)=\<psi\>(\<phi\>(r.x))=\<psi\>(r.\<phi\>(x))=r.\<psi\>(\<phi\>(x))=r.(\<psi\>\<circ\>\<phi\>)(x)>
    for all <math|r\<in\>R> and <math|x\<in\>M> <em|i.e.>
    <math|\<psi\>\<circ\>\<phi\>\<in\>L(M,P)> as claimed. Finally, the
    identity map <math|\<iota\>\<#2236\>M\<rightarrow\>M> is <math|R>-linear
    since <math|\<iota\>(r.x)=r.x=r.\<iota\>(x)> for all <math|r\<in\>R> and
    <math|x\<in\>M>, so <math|1<rsub|Hom(M,M)>\<in\>L(M,M)>. <math|L(M,M)> is
    closed under differences by the first part of the proposition, and is
    closed under products by what we just showed. By the subring test
    <math|L(M,M)> is a subring of <math|Hom(M,M)> as claimed.
  </proof>

  <\remark>
    If <math|R> is a commutative ring then we can define a scalar
    multiplication on <math|L(M,N)> by <math|(r.\<phi\>)(x)\<assign\>\<phi\>(r.x)>
    giving it the structure of an <math|R>-module.

    <with|font|Segoe UI Emoji|\<#26A0\>>In Exercise III.10 there is an
    example of a ring <math|R> and <math|R>-module <math|M> such that the
    commutative group <math|L(M,M)> cannot be given the structure of an
    <math|R>-module.
  </remark>

  <subsection|Isomorphisms and submodules>

  We say that <math|\<phi\>:M\<rightarrow\>N> is an <strong|<math|R>-linear
  isomorphism> if it is <math|R>-linear and it has an <math|R>-linear
  inverse.

  <\observation>
    If <math|\<phi\>:M\<rightarrow\>N> is an <math|R>-linear bijection then
    its inverse map is a group homomorphism, and
    <math|\<phi\><rsup|\<minus\>1>(\<lambda\>.x)=\<phi\><rsup|\<minus\>1>(\<lambda\>.\<phi\>(\<phi\><rsup|\<minus\>1>(x)))=\<phi\><rsup|\<minus\>1>(\<phi\>(\<lambda\>.\<phi\><rsup|\<minus\>1>(x)))=\<lambda\>.\<phi\><rsup|\<minus\>1>(x)>
    so that <math|\<phi\>> is an <math|R>-linear isomorphism.
  </observation>

  <\example>
    The map

    <\equation*>
      R<rsup|n>\<rightarrow\>R<rsup|n><rsub|<text|col>>;<around*|(|r<rsub|1>,\<ldots\>,r<rsub|n>|)>\<mapsto\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|1|1|cell-rborder|0ln>|<table|<row|<cell|r<rsub|1>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|n>>>>>>|)>
    </equation*>

    is an <math|R>-linear bijection between the <math|R>-module
    <math|R<rsup|n>> and the <math|R>-module
    <math|R<rsup|n><rsub|<text|col>>>, and hence an <math|R>-linear
    isomorphism.
  </example>

  <\example>
    The map <math|\<bbb-Q\>\<rightarrow\>\<bbb-Q\>;x\<mapsto\>2x> is a
    <math|\<bbb-Z\>>-linear bijection from the <math|\<bbb-Z\>>-module
    <math|\<bbb-Q\>> to itself arising via scalar multiplication as in
    Example 4.19. <with|font|Segoe UI Emoji|\<#26A0\>>The inverse map, while
    also <math|\<bbb-Z\>>-linear does <em|not> arise via scalar
    multiplication when <math|\<bbb-Q\>> is considered as a
    <math|\<bbb-Z\>>-module since there is no integer <math|z\<in\>\<bbb-Z\>>
    such that <math|2z*x=x> for all <math|x\<in\>\<bbb-Q\>>.
  </example>

  An <math|R>-module <math|N> is a <strong|submodule> of an <math|R>-module
  <math|M> if the map <math|j:N\<rightarrow\>M;x\<mapsto\>x> is a
  well-defined <math|R>-linear map. We write <math|N\<leqslant\>M> and also
  say that <math|N> is <strong|proper> if <math|M\<neq\>N>.

  <\example>
    <dueto|Example 4.2, contd.>When <math|V> is a vector space, a submodule
    of <math|V> is exactly a subspace of <math|V>.
  </example>

  <\example>
    <dueto|Left ideals are submodules><math|I> is a left ideal in a ring
    <math|R> if and only if <math|I> is a submodule of the <math|R>-module
    <math|R>.
  </example>

  <\example>
    The ideal \<langle\>2\<rangle\> in the ring <math|\<bbb-Z\>> is a proper
    submodule of the <math|\<bbb-Z\>>-module <math|\<bbb-Z\>> and it is
    <math|\<bbb-Z\>>-linearly isomorphic to the <math|\<bbb-Z\>>-module
    <math|\<bbb-Z\>> via <math|\<bbb-Z\>\<rightarrow\>\<langle\>2\<rangle\>;z\<mapsto\>2z>.

    <with|font|Segoe UI Emoji|\<#26A0\>>This is quite different from the
    situation with vector spaces: the only subspaces of the
    <math|\<bbb-F\>>-vector space <math|\<bbb-F\>> are {0} and
    <math|\<bbb-F\>>.
  </example>

  <\lemma>
    <dueto|Submodule test>Suppose that <math|M> is an <math|R>-module and
    <math|\<emptyset\>\<neq\>N\<subset\>M> has <math|x+y\<in\>N> for all
    <math|x,y\<in\>N>, and <math|r.x\<in\>N> whenever <math|x\<in\>N> and
    <math|r\<in\>R>. Then addition on <math|M> and scalar multiplication of
    <math|R> on <math|M> restrict to well-defined operations on <math|N>
    giving it the structure of a submodule of <math|M>.
  </lemma>

  <\proof>
    First, <math|\<minus\>1\<in\>R> and <math|(\<minus\>1).x=\<minus\>x> for
    all <math|x\<in\>M> so that by the hypotheses, <math|N> is non-empty and
    <math|x\<minus\>y\<in\>N> whenever <math|x,y\<in\>N>. It follows that
    <math|N> with addition on <math|M> restricted to <math|N>, is a subgroup
    of <math|M> by the subgroup test. Since <math|r.x\<in\>N> whenever
    <math|r\<in\>R> and <math|x\<in\>N>, scalar multiplication of <math|R> on
    <math|M> restricts to a well-defined function
    <math|R\<times\>N\<rightarrow\>N> which <em|a fortiori> satisfies
    (M1)\U(M4). Finally, the inclusion map is <math|R>-linear and the result
    is proved.
  </proof>

  As with rings, given a subset satisfying the hypotheses of the above lemma,
  we make the common abuse of calling it a submodule on the understanding
  that we are referring to the induced operations.

  <subsection|Quotients and the First Isomorphism Theorem>

  <\theorem>
    <dueto|Quotient modules>Suppose that <math|M> is an <math|R>-module and
    <math|N> is a submodule of <math|M>. Then the commutative group
    <math|M/N> may be endowed with the structure of an <math|R>-module such
    that <math|q:M\<rightarrow\>M/N;x\<mapsto\>x+N> is an <math|R>-linear
    surjection with kernel <math|N>.
  </theorem>

  <\proof>
    Since <math|N> is a commutative subgroup of <math|M> we have that
    <math|M/N> is a commutative group and the map <math|q> is a surjective
    homomorphism with kernel <math|N> by definition of the quotient group.
    Define a scalar multiplication of <math|R> on <math|M/N> by
    <math|r.(x+N)\<assign\>r.x+N>. This is well defined: if <math|x+N=y+N>
    then <math|x+n=y+n<rprime|'>> for some <math|n,n<rprime|'>\<in\>N>, so
    <math|r.x+r.n=r.y+r.n<rprime|'>>, but since <math|N> is a submodule
    <math|r.n,r.n<rprime|'>\<in\>N> and hence <math|r.x+N=r.y+N> as required.

    (M1) follows since <math|1.(x+N)=(1.x)+N=x+N> for all <math|x\<in\>M> by
    (M1) for the scalar multiplication on <math|M>. (M2) follows since
    <math|r.(s.(x+N))=r.(s.x+N)=(r.(s.x))+N=(r*s).x+ N=(r*s).(x+N)> for all
    <math|r,s\<in\>R> and <math|x\<in\>M> by (M2) for the scalar
    multiplication on <math|M>. (M3) follows by (M3) for the scalar
    multiplication on <math|M> and the fact that <math|q> is a homomorphism
    so <math|(r+s).(x+N)=(r+s).x+N=((r.x)+(s.x))+N=(r.x+N)+(s.x+N)=r.(x+N)+s.(x+N)>
    for all <math|r,s\<in\>R> and <math|x\<in\>M>. Finally, (M4) follows by
    (M4) for the scalar multiplication on <math|M> and the fact that <math|q>
    is a homomorphism so <math|r.((x+N)+(y+N))=r.((x+y)+N)=r.(x+y)+N=((r.x)+(r.y))+N=(r.x+N)+(r.y+N)>
    for all <math|r\<in\>R> and <math|x,y\<in\>M>.

    Finally, it remains to note that <math|q> is <math|R>-linear by
    definition and the result is proved.
  </proof>

  <\remark>
    Since the map <math|q> above is a surjective <math|R>-linear map the
    scalar multiplication on <math|M/N> is determined by <math|q>:
    <math|r.(x+N)=r.x+N> for all <math|x\<in\>M> and <math|r\<in\>R>, where
    the first . is scalar multiplication in <math|M/N>, and the second in
    <math|M>.

    By the <math|R>-module <math|M/N> we mean the module structure of this
    theorem.
  </remark>

  <\theorem>
    <dueto|First Isomorphism Theorem for modules>Suppose that
    <math|\<phi\>:M\<rightarrow\>N> is <math|R>-linear. Then <math|ker
    \<phi\>> is a submodule of <math|M>; <math|Im \<phi\>> is a submodule of
    <math|N>; and the map

    <\equation*>
      <wide|\<phi\>|~>:M/ker \<phi\>\<rightarrow\>N;x+ker
      \<phi\>\<mapsto\>\<phi\>(x)
    </equation*>

    is an injective <math|R>-linear map with image <math|Im \<phi\>>. In
    particular, <math|Im \<phi\>\<cong\>M/ker \<phi\>>.
  </theorem>

  <\proof>
    Both <math|ker \<phi\>> and <math|Im \<phi\>> are subgroups of the
    additive groups of <math|M> and <math|N> respectively by the First
    Isomorphism Theorem for groups since <math|\<phi\>> is, in particular, a
    group homomorphism. Therefore by the submodule test <math|ker \<phi\>>
    and <math|Im \<phi\>> are submodules since if <math|x\<in\>ker \<phi\>>
    then <math|0<rsub|N>=r.0<rsub|N>=r.\<phi\>(x)=\<phi\>(r.x)> and so
    <math|r.x\<in\>ker \<phi\>>; and if <math|x\<in\>Im \<phi\>> then there
    is <math|y\<in\>M> such that <math|x=\<phi\>(y)> and so
    <math|r.x=r.\<phi\>(y)=\<phi\>(r.y)\<in\>Im \<phi\>>.

    By Theorem 4.29 <math|M/ker \<phi\>> is an <math|R>-module.
    <math|<wide|\<phi\>|~>> is an injective well-defined group homomorphism
    by the First Isomorphism Theorem for groups. It remains to check that it
    is linear which follows since <math|<wide|\<phi\>|~>(r.(x+ker
    \<phi\>))=<wide|\<phi\>|~>((r.x)+ker \<phi\>)=\<phi\>(r.x)=r.\<phi\>(x)=r.<wide|\<phi\>|~>(x+ker
    \<phi\>)> for all <math|r\<in\>R> and <math|x\<in\>M>.
  </proof>

  <section|Free modules>

  <subsection|Generation>

  For an <math|R>-module <math|M> and <math|\<Lambda\>\<subset\>M> we write\ 

  <\equation*>
    \<langle\>\<Lambda\>\<rangle\>\<assign\>{r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>:n\<in\>\<bbb-N\><rsub|0>,
    x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>\<Lambda\>,
    r<rsub|1>,\<ldots\>,r<rsub|n>\<in\>R}.
  </equation*>

  This is a submodule of <math|M> by the submodule test, and we call this
  submodule the <strong|module generated by <math|\<Lambda\>>>. For
  <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>M> we write

  <\equation*>
    \<langle\>x<rsub|1>,\<ldots\>,x<rsub|n>\<rangle\>\<assign\>{r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>:r<rsub|1>,\<ldots\>,r<rsub|n>\<in\>R},
  </equation*>

  and since <math|0<rsub|R>.x<rsub|i>=0<rsub|M>>, the identity of the
  additive group of <math|M>, we have that
  <math|\<langle\>x<rsub|1>,\<ldots\>,x<rsub|n>\<rangle\>=\<langle\>{x<rsub|1>,\<ldots\>,x<rsub|n>}\<rangle\>>.

  <\example>
    An <math|R>-module <math|M> is generated by the set <math|M> itself, and
    <math|M> is generated by the empty set if and only if it is the zero
    <math|R>-module.
  </example>

  <\example>
    <dueto|Vector spaces, contd.>For <math|\<bbb-F\>> a field, <math|V> an
    <math|\<bbb-F\>>-module, and <math|\<Lambda\>\<subset\>V> the submodule
    generated by <math|\<Lambda\>> is the same as subspace spanned by
    <math|\<Lambda\>>.
  </example>

  <\example>
    Write <math|e<rsub|i>\<assign\>(0,\<ldots\>,0,1,0,\<ldots\>,0)> for the
    elements of <math|R<rsup|n>> with <math|1<rsub|R>> in the ith position
    and <math|0<rsub|R>> elsewhere. Similarly write <math|e<rsup|t><rsub|i>>
    for the column vector in <math|R<rsup|n><rsub|<text|col>>> with
    <math|1<rsub|R>> in the <math|i>th row and <math|0<rsub|R>>s elsewhere.

    <math|{e<rsub|1>,\<ldots\>,e<rsub|n>}> generates the <math|R>-module
    <math|R<rsup|n>> since if <math|r\<in\>\<bbb-R\><rsup|n>> then
    <math|r=r<rsub|1>.e<rsub|1>+\<cdots\>+r<rsub|n>.e<rsub|n>>, and similarly
    <math|{e<rsup|t><rsub|1>,\<ldots\>,e<rsup|t><rsub|n>}> generates
    <math|R<rsup|n><rsub|<text|col>>>.
  </example>

  If there is a finite set <math|\<Lambda\>> such that <math|M> is generated
  by <math|\<Lambda\>> then we say that <math|M> is <strong|finitely
  generated>. If <math|M> is generated by a set of size 1 we say that
  <math|M> is <strong|cyclic>.

  <\example>
    <dueto|Commutative groups, contd.>A commutative group <math|M> is cyclic
    if and only if the <math|\<bbb-Z\>>-module <math|M> is cyclic.

    For <math|M> a <em|finite> commutative group, the <math|\<bbb-Z\>>-module
    <math|M> is finitely generated since it is generated by the finite set
    <math|M>.
  </example>

  <\example>
    The <math|\<bbb-Z\>>-module <math|\<bbb-Q\>> is not cyclic. Indeed, for
    any <math|q\<in\>\<bbb-Q\><rsup|\<ast\>>> there is no
    <math|z\<in\>\<bbb-Z\>> such that <math|z*q=q/2>, and since
    <math|\<bbb-Q\>\<neq\>\<langle\>0\<rangle\>> the claim follows.
    <with|font|Segoe UI Emoji|\<#26A0\>>The <math|\<bbb-Q\>>-module
    <math|\<bbb-Q\>> is cyclic and it is generated by any set <math|{q}> with
    <math|q\<in\>\<bbb-Q\><rsup|\<ast\>>>.
  </example>

  <\example>
    For <math|R> a ring, the <math|R>-module <math|R> is cyclic \U it is
    generated by 1 \U and if <math|K> a submodule of the <math|R>-module
    <math|R> (equivalently <math|K> is a left ideal in the ring <math|R>),
    the quotient module <math|R/K> is cyclic \U it is generated by
    <math|1+K>.
  </example>

  In fact <em|every> cyclic <math|R>-module is isomorphic to a module of this
  form: if <math|M> is a cyclic <math|R>-module then the map
  <math|\<phi\>:R\<rightarrow\>M;r\<mapsto\>r.x> is surjective and
  <math|R>-linear, and so by the First Isomorphism Theorem there is a
  submodule <math|K> of the <math|R>-module <math|R> \U in this case
  <math|ker \<phi\>> \U such that <math|R/K> is <math|R>-linearly isomorphic
  to <math|M>.

  <\observation>
    The <math|R>-linear image of an <math|R>-module generated by a set of
    size <math|n> is generated by a set of size <math|n> [image of a
    generating set generates the image].
  </observation>

  <\proposition>
    Suppose that <math|\<phi\>:M\<rightarrow\>N> is an <math|R>-linear map
    and <math|Im \<phi\>> and <math|ker \<phi\>> are generated by sets of
    sizes <math|n> and <math|m> respectively. Then <math|M> is generated by a
    set of size <math|n+m>.
  </proposition>

  <\proof>
    Let <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>M> be such that
    <math|\<phi\>(x<rsub|1>),\<ldots\>,\<phi\>(x<rsub|n>)> generate <math|Im
    \<phi\>>, and let <math|x<rsub|n+1>,\<ldots\>,x<rsub|n+m>> generate
    <math|ker \<phi\>>. Then if <math|x\<in\>M>, there are elements
    <math|r<rsub|1>,\<ldots\>,r<rsub|n>\<in\>R> such that
    <math|\<phi\>(x)=r<rsub|1>.\<phi\>(x<rsub|1>)+\<cdots\>+r<rsub|n>.\<phi\>(x<rsub|n>)>,
    and hence <math|\<phi\>(x\<minus\>r<rsub|1>.x<rsub|1>\<minus\>\<cdots\>\<minus\>r<rsub|n>.x<rsub|n>)=0>
    and so there are elements <math|r<rsub|n+1>,\<ldots\>,r<rsub|n+m>\<in\>R>
    with <math|x\<minus\>r<rsub|1>.x<rsub|1>\<minus\>\<cdots\>\<minus\>r<rsub|n>.x<rsub|n>=r<rsub|n+1>.x<rsub|n+1>+\<cdots\>+r<rsub|n+m>.x<rsub|n+m>>.
    Rearranging the result is proved.
  </proof>

  <\example>
    <dueto|Vector spaces, contd.>The proof above is modelled on a proof of
    the Rank Nullity theorem, and in fact since a basis for a vector space is
    certainly a spanning and so generating set, it tells us that if <math|V>
    is a vector space and <math|T:V\<rightarrow\>W> is linear with finite
    rank and nullity then <math|dim V\<leqslant\>rk(T)+n(T)>. The
    Rank-Nullity Theorem is the stronger claim that we have equality here.
  </example>

  In an <math|R>-module <math|M>, we say <math|\<cal-E\>\<subset\>M> is a
  <strong|minimal generating set> if <math|\<cal-E\>> generates <math|M> and
  no proper subset of <math|\<cal-E\>> generates <math|M>.

  <\observation>
    A finitely generated <math|R>-module <math|M> contains a minimal
    generating set by induction.
  </observation>

  <\example>
    <with|font|Segoe UI Emoji|\<#26A0\>>Minimal generating sets need not
    exist: Exercise III.1 asks for a proof that the <math|\<bbb-Z\>>-module
    <math|\<bbb-Q\>> does not have a minimal generating set. In particular,
    in view of the preceding observation, the <math|\<bbb-Z\>>-module
    <math|\<bbb-Q\>> is not finitely generated.
  </example>

  <\example>
    The set <math|{2,3}> is a generating set for the <math|\<bbb-Z\>>-module
    <math|\<bbb-Z\>>, and no proper subset is generating so it is a minimal
    generating set. <with|font|Segoe UI Emoji|\<#26A0\>>There are smaller
    generating sets of <math|\<bbb-Z\>>\V <math|{1}> and
    <math|{\<minus\>1}>.[minimal generating set may not have minimal size]
  </example>

  <\proposition>
    Suppose that <math|M> is a finitely generated <math|R>-module. Then every
    generating set for <math|M> contains a finite subset that is also a
    generating set. In particular, every minimal generating set is finite.
  </proposition>

  <\proof>
    Let <math|{x<rsub|1>,\<ldots\>,x<rsub|n>}> generate <math|M> and suppose
    that <math|\<cal-E\>> is a generating set for <math|M>. For each
    <math|1\<leqslant\>i\<leqslant\>n> there is a finite subset
    <math|S<rsub|i>\<subset\>\<cal-E\>> such that
    <math|x<rsub|i>\<in\>\<langle\>S<rsub|i>\<rangle\>>, and hence
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>\<langle\><big|cup><rsup|n><rsub|i=1>
    S<rsub|i>\<rangle\>>. Since <math|{x<rsub|1>,\<ldots\>,x<rsub|n>}>
    generates <math|M> we have <math|\<cal-E\>\<subset\>M=\<langle\>x<rsub|1>,\<ldots\>,x<rsub|n>\<rangle\>\<subset\><around*|\<langle\>|<around*|\<langle\>|<big|cup><rsup|n><rsub|i=1>
    S<rsub|i>|\<rangle\>>|\<rangle\>>=<around*|\<langle\>|<big|cup><rsup|n><rsub|i=1>
    S<rsub|i>|\<rangle\>>>. However, <math|<big|cup><rsup|n><rsub|i=1>
    S<rsub|i>\<in\>\<cal-E\>>, and a finite union of finite sets is finite as
    required.
  </proof>

  <subsection|Linear independence>

  For an <math|R>-module <math|M> we say that a finite sequence
  <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>M> is <strong|(<math|R>-)linearly
  independent> if whenever <math|r<rsub|1>,\<ldots\>,r<rsub|n>\<in\>R> have
  <math|r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>=0<rsub|M>> we have
  <math|r<rsub|1>,\<ldots\>,r<rsub|n>=0<rsub|R>>. A set \<Lambda\> is
  <strong|(<math|R>-)linearly independent> if for every
  <math|n\<in\>\<bbb-N\><rsub|0>>, <math|x<rsub|1>,\<ldots\>,x<rsub|n>> is
  <math|R>-linearly independent for every sequence of <em|distinct>
  <math|x<rsub|1>,\<ldots\>,x<rsub|n>\<in\>\<Lambda\>.>

  Sets and sequences are <strong|(<math|R>-)linearly dependent> if they are
  not <math|R>-linearly independent.

  <\example>
    In an <math|R>-module <math|M> the empty set or empty sequence is
    <math|R>-linearly independent.
  </example>

  <\example>
    <dueto|Vector spaces, contd.>A subset of a vector space is linearly
    independent in the usual sense if and only if it is linearly independent
    in the sense here.
  </example>

  <\example>
    <dueto|Example 5.3, cont.><math|e<rsub|1>,\<ldots\>,e<rsub|n>> are
    <math|R>-linearly independent in <math|R<rsup|n>>: if
    <math|r<rsub|1>.e<rsub|1>+\<cdots\>+r<rsub|n>.e<rsub|n>=0> for
    <math|r<rsub|1>,\<ldots\>,r<rsub|n>\<in\>R> then
    <math|r<rsub|1>,\<ldots\>,r<rsub|n>=0>, and similarly for
    <math|<math|e<rsup|t><rsub|1>,\<ldots\>,e<rsup|t><rsub|n>>> in
    <math|R<rsup|n><rsub|<text|col>>>.
  </example>

  <\example>
    <dueto|Commutative groups, contd.>If <math|M> is a finite commutative
    group then by Lagrange's Theorem <math|<around*|\||M|\|>.x=0> for all
    <math|x> in the <math|\<bbb-Z\>>-module <math|M>, and hence there are no
    non-empty <math|\<bbb-Z\>>-linearly independent subsets of <math|M>.
  </example>

  <\example>
    <dueto|torsion>The <math|\<bbb-Z\>>-module <math|\<bbb-Q\>> has no
    <math|\<bbb-Z\>>-linearly independent subset of size 2. Indeed, suppose
    that <math|e<rsub|1>,e<rsub|2>\<in\>\<bbb-Q\>> were a
    <math|\<bbb-Z\>>-linearly independent sequence with
    <math|e<rsub|2>\<neq\>0>. There is <math|z\<in\>\<bbb-Z\><rsup|\<ast\>>>
    such that <math|z*e<rsub|1>,z*e<rsub|2>\<in\>\<bbb-Z\>>, and hence
    <math|(z*e<rsub|2>).e<rsub|1>+(\<minus\>z*e<rsub|1>).e<rsub|2>=0> but
    <math|z*e<rsub|2>\<neq\>0> so <math|e<rsub|1>,e<rsub|2>> is
    <math|\<bbb-Z\>>-linearly dependent \U a contradiction.
  </example>

  <subsection|Bases>

  For an <math|R>-module <math|M> we say that <math|\<cal-E\>> is a
  <strong|basis> for <math|M> if it is a linearly independent generating set
  for <math|M>. A module with a basis is called <strong|free>.

  <\example>
    The zero <math|R>-module has the empty set as a basis and so is free.

    <with|font|Segoe UI Emoji|\<#26A0\>>If <math|R> is trivial then {0} is
    also a basis since it is <math|R>-linearly independent.
  </example>

  <\example>
    <dueto|Commutative groups, contd.>If <math|M> is a non-trivial finite
    commutative group then the <math|\<bbb-Z\>>-module <math|M> is not free
    since the only independent sets are empty and the module generated by the
    empty set has only one element: zero.
  </example>

  <\example>
    The <math|\<bbb-Z\>>-module <math|\<bbb-Q\>> is <em|not> free: If it were
    it would have a basis <math|\<cal-E\>>. If <math|\<cal-E\>> had more than
    one element then it would contain two linearly independent elements
    contradicting the conclusion of Example 5.18; if it had strictly fewer
    than two elements then <math|\<bbb-Q\>> would be cyclic contradicting the
    conclusion of Example 5.5.
  </example>

  <\example>
    <dueto|Example 5.3, contd.>In view of Examples 5.3 & 5.16,
    <math|{e<rsub|1>,\<ldots\>,e<rsub|n>}> is a basis for the <math|R>-module
    <math|R<rsup|n>> and <math|{e<rsup|t><rsub|1>,\<ldots\>,e<rsup|t><rsub|n>}>
    is a basis for the <math|R>-module <math|R<rsup|n><rsub|<text|col>>> \U
    these are both free modules.
  </example>

  <\example>
    <dueto|Example 4.15, contd.>If <math|{x<rsub|1>,\<ldots\>,x<rsub|n>}> is
    a basis for the <math|R>-module <math|M> then the linear map
    <math|\<Phi\><rsub|x>:R<rsup|n>\<rightarrow\>M;r\<mapsto\>r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>>
    is injective since <math|{x<rsub|1>,\<ldots\>,x<rsub|n>}> is linearly
    independent, and surjective since <math|{x<rsub|1>,\<ldots\>,x<rsub|n>}>
    is a generating set, hence <math|\<Phi\><rsub|x>> is an <math|R>-linear
    isomorphism.
  </example>

  <\proposition>
    Suppose that <math|M> is an <math|R>-module with a basis
    <math|\<cal-E\>>. Then <math|\<cal-E\>> is a minimal generating set. In
    particular, if <math|M> is finitely generated then <math|\<cal-E\>> is
    finite.
  </proposition>

  <\proof>
    Suppose that <math|\<cal-E\><rprime|'>\<subset\>\<cal-E\>> generates
    <math|M> and <math|e\<in\>\<cal-E\>\<setminus\>\<cal-E\><rprime|'>>.
    Since <math|\<cal-E\><rprime|'>> generates <math|M>,
    <math|1.e=e\<in\>\<langle\>\<cal-E\><rprime|'>\<rangle\>> and so
    <math|{e}\<cup\>\<cal-E\><rprime|'>> is linearly dependent. But this is
    contained in <math|\<cal-E\>> which is linearly independent and linear
    independence is preserved under passing to subsets. This contradiction
    establishes the first claim.

    For the last part \PSuppose <math|M> is finitely genereated, then
    <math|M> has a finite basis\Q: Let <math|\<cal-E\>> be a basis for
    <math|M>, then <math|\<cal-E\>> is minimal generating set by the first
    part, and <math|\<cal-E\>> contains a finite generating set
    <math|\<cal-E\><rprime|'>> by Proposition 5.13. But by minimality
    <math|\<cal-E\>=\<cal-E\><rprime|'>>.
  </proof>

  <\example>
    The set <math|{2,3}> is a minimal generating set for the
    <math|\<bbb-Z\>>-module <math|\<bbb-Z\>>, but it is not linearly
    independent and so not a basis.
  </example>

  <\example>
    <dueto|Vector spaces, contd.>A minimal generating set in a vector space
    is linearly independent and so a basis. In particular, any finitely
    generated vector space has a minimal generating set and so has a finite
    basis. In other words, every finitely generated vector space has a basis,
    by contrast with the case of more general modules (Example 5.20).
  </example>

  <\remark>
    <with|font|Segoe UI Emoji|\<#26A0\>>In a vector space any two finite
    bases have the same size \U this is sometimes called the Dimension
    Theorem. For more general rings, finite bases of modules over those rings
    need not have the same size: the zero module over the trivial ring has
    \<emptyset\> and {0} as bases of sizes 0 and 1 respectively; Exercise
    III.9 gives an example of a non-trivial ring and a module over that ring
    with bases of sizes 1 and 2.
  </remark>

  <subsection|Presentations>

  A quotient of a finitely generated module is finitely generated, but the
  same is not true of submodules:

  <\example>
    In Exercise II.4 we saw that <math|<wide|\<bbb-Z\>|\<wide-bar\>>>
    contains an ideal that is not finitely generated, and this ideal is
    therefore a submodule of the cyclic <math|<wide|\<bbb-Z\>|\<wide-bar\>>>-module
    <math|<wide|\<bbb-Z\>|\<wide-bar\>>> that is not finitely generated.
  </example>

  A matrix <math|A\<in\>M<rsub|n>(R)> is said to be <strong|upper triangular>
  if <math|A<rsub|i,j>=0> whenever <math|j\<less\>i>.

  <\proposition>
    Suppose that <math|R> is a PID and <math|M\<leqslant\>R<rsup|n>>. Then
    there is an upper triangular <math|A\<in\>M<rsub|n>(R)> such that
    <math|M=R<rsup|n>A=<around*|{|x*A:x\<in\>R<rsup|n>|}>>.
  </proposition>

  <\proof>
    For each <math|1\<leqslant\>i\<leqslant\>n> the set
    <math|M<rsub|i>\<assign\>{x<rsub|i>\<in\>R:x\<in\>M<text| and
    >x<rsub|1>,\<ldots\>,x<rsub|i\<minus\>1>=0}> is a submodule of the
    <math|R>-module <math|R> and since <math|R> is a PID every such submodule
    is an ideal and generated by one element of <math|R>. Let
    <math|A\<in\>M<rsub|n>(R)> be such that <math|(0,\<ldots\>,0,
    A<rsub|i,i>,\<ldots\>,A<rsub|i,n>)\<in\>M> has <math|A<rsub|i,i>>
    generating <math|M<rsub|i>>.

    By design <math|A> is upper triangular and every row of <math|A> is in
    <math|M>, so any linear combination of rows of <math|A> is in <math|M> \U
    in other words <math|R<rsup|n>A\<subset\>M>. In the other direction,
    suppose that <math|x\<in\>M\<setminus\>R<rsup|n>A> has
    <math|i\<leqslant\>n> maximal such that
    <math|x<rsub|1>,\<ldots\>,x<rsub|i\<minus\>1>=0>. Since <math|x> is not
    equal to 0 we have <math|A<rsub|i,i>\<divides\>x<rsub|i>>, say
    <math|x<rsub|i>=z*A<rsub|i,i>>. Then <math|x<rprime|'>\<assign\>x\<minus\>(0,\<ldots\>,0,z,0,\<ldots\>,0)A\<in\>M\<setminus\>R<rsup|n>A>
    but <math|x<rprime|'><rsub|1>,\<ldots\>,x<rprime|'><rsub|i>= 0>
    contradicting the maximality.
  </proof>

  <\remark>
    Being free and finitely generated are properties that are preserved by
    isomorphisms so in particular, if <math|M> is a submodule of a free and
    finitely generated module over a PID then it is finitely generated.
  </remark>

  <\example>
    <dueto|Vector spaces, contd.>For <math|V> a finitely generated vector
    space, any subspace of <math|V> is also finitely generated by the above
    since <math|V> itself is free and every field is a PID.
  </example>

  An <math|R>-module <math|M> has a <strong|finite presentation with
  presentation matrix> <math|A\<in\>M<rsub|m,n>(R)> if there is an
  <math|R>-linear isomorphism <math|\<Phi\>:R<rsup|n>/R<rsup|m>A\<rightarrow\>M>.

  <\example>
    For <math|M> an <math|R>-module with basis
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>>, the linear map
    <math|><math|R<rsup|n>\<rightarrow\>M;r\<mapsto\>r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>>
    is an <math|R>-linear isomorphism. For any
    <math|m\<in\>\<bbb-N\><rsub|0>>, we have
    <math|R<rsup|m>0<rsub|m\<times\>n>={0<rsub|R<rsup|n>>}> and hence by the
    First Isomorphism Theorem <math|M> has a finite presentation with
    presentation matrix <math|0<rsub|m\<times\>n>>.
  </example>

  <\observation>
    A module with a finite presentation is finitely generated. On the other
    hand, Exercise III.6 gives an example of a finitely generated module that
    does <em|not> have a finite presentation.
  </observation>

  <\example>
    For <math|R> a PID and <math|M> an <math|R>-module generated by
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>> there is an <math|R>-linear
    surjection <math|R<rsup|n>\<rightarrow\>M;r\<mapsto\>r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>>.
    By Proposition 5.29 the kernel of this map is <math|R<rsup|n>A> for some
    upper triangular <math|A\<in\>M<rsub|n>(R)>, and hence by the First
    Isomorphism Theorem <math|M> has a finite presentation with presentation
    matrix <math|A>.
  </example>

  <section|Elementary operations and the Smith normal form>

  There are three types of <strong|elementary column (resp. row) operation>
  that can be applied to matrices in <math|M<rsub|n,m>(R)> \U transvections,
  dilations, and interchanges \U and these correspond to right (resp. left)
  multiplication by matrices from <math|M<rsub|m>(R)> and <math|M<rsub|n>(R)>
  respectively.

  Write <math|E<rsub|n>(i,j)> for the matrix in <math|M<rsub|n>(R)> with
  <math|0<rsub|R>>s everywhere except for row <math|i> and column <math|j>
  where the entry is <math|1<rsub|R>>. Then <math|E<rsub|n>(i, j)E<rsub|n>(k,
  l)=E<rsub|n>(i,l)> if <math|j=k> and <math|E<rsub|n>(i,
  j)E<rsub|n>(k,l)=0<rsub|n\<times\>n>> if <math|j\<neq\>k>.

  <subsection|Transvections>

  For <math|1\<leqslant\>i,j\<leqslant\>m> with <math|i\<neq\>j> and
  <math|\<lambda\>\<in\>R> put <math|T<rsub|m>(i,j;\<lambda\>)=I<rsub|m>+\<lambda\>.E<rsub|m>(i,j)>
  (where . is the scalar multiplication of the <math|R>-module
  <math|M<rsub|m>(R)>) so that

  <\equation*>
    T<rsub|m>(i,j;\<lambda\>)T<rsub|m>(i,j;\<minus\>\<lambda\>)=I<rsub|m>=T<rsub|m>(i,j;\<minus\>\<lambda\>)T<rsub|m>(i,j;\<lambda\>).
  </equation*>

  Given <math|A\<in\>M<rsub|n,m>(R)>, the matrix
  <math|A*T<rsub|m>(i,j;\<lambda\>)> is the matrix <math|A> with the
  <math|i>th column times <math|\<lambda\>> added to the <math|j>th column;
  we write this

  <\equation*>
    A<long-arrow|\<rubber-rightarrow\>|c<rsub|j>\<mapsto\>c<rsub|j>+c<rsub|i>\<lambda\>>A*T<rsub|m>(i,j;\<lambda\>).
  </equation*>

  Similarly the matrix <math|T<rsub|n>(i,j;\<lambda\>)A> is the matrix
  <math|A> with <math|\<lambda\>> times the <math|j>th row added to the
  <math|i>th row; we write this

  <\equation*>
    A*<long-arrow|\<rubber-rightarrow\>|r<rsub|i>\<mapsto\>r<rsub|i>+\<lambda\>r<rsub|j>>T<rsub|n>(i,j;\<lambda\>)A.
  </equation*>

  <subsection|Dilations>

  For <math|1\<leqslant\>i\<leqslant\>m> and <math|u\<in\>U(R)> let
  <math|D<rsub|m>(i;u)=I<rsub|m>+(u\<minus\>1).E<rsub|m>(i,i)> so that

  <\equation*>
    D<rsub|m>(i;u)D<rsub|m>(i;u<rsup|\<minus\>1>)=I<rsub|m>=D<rsub|m>(i;u<rsup|\<minus\>1>)D<rsub|m>(i;u).
  </equation*>

  The matrix <math|A*D<rsub|m>(i;u)> is the matrix with the <math|i>th column
  replaced by the ith column times <math|u> and as above we write this and
  the corresponding row operation as

  <\equation*>
    A<long-arrow|\<rubber-rightarrow\>|c<rsub|i>\<mapsto\>c<rsub|i>u>A*D<rsub|m>(i;u)<text|
    and >A<long-arrow|\<rubber-rightarrow\>|r<rsub|i>\<mapsto\>u*r<rsub|i>>D<rsub|n>(i;u)A.
  </equation*>

  <subsection|Interchanges>

  For <math|1\<leqslant\>i,j\<leqslant\>m> let
  <math|S<rsub|m>(i,j)=I<rsub|m>+E<rsub|m>(i,j)+E<rsub|m>(j,i)\<minus\>E<rsub|m>(i,i)\<minus\>E<rsub|m>(j,j)>
  so that <math|S<rsub|m>(i,j)<rsup|2>=I<rsub|m>>. The matrix
  <math|A*S<rsub|m>(i,j)> is the matrix <math|A> with columns <math|i> and
  <math|j> swapped and as above we write

  <\equation*>
    A<long-arrow|\<rubber-rightarrow\>|c<rsub|i>\<leftrightarrow\>c<rsub|j>>A*S<rsub|m>(i,j)<text|
    and >A<long-arrow|\<rubber-rightarrow\>|r<rsub|i>\<leftrightarrow\>r<rsub|j>>S<rsub|n>(i,j)A
  </equation*>

  for this and the corresponding row operation.

  <\remark>
    We write <math|GL<rsub|n>(R)> for the group <math|U(M<rsub|n>(R))>, and
    <math|GE<rsub|n>(R)> for the subgroup of <math|GL<rsub|n>(R)> generated
    by the transvections, dilations, and interchanges.

    In general <math|GL<rsub|2>(R)\<neq\>GE<rsub|2>(R)>, though this can be
    hard to show. An example, taken from [Coh66, p23], is the ring
    <math|\<bbb-Z\>[\<theta\>]> where <math|\<theta\><rsup|2>\<minus\>\<theta\>+5=0>.
    Here the matrix

    <\equation*>
      A\<assign\><matrix|<tformat|<table|<row|<cell|3\<minus\>\<theta\>>|<cell|2+\<theta\>>>|<row|<cell|\<minus\>3\<minus\>2\<theta\>>|<cell|5\<minus\>2\<theta\>>>>>>
    </equation*>

    is in <math|GL<rsub|2>(\<bbb-Z\>[\<theta\>])> but not in
    <math|GE<rsub|2>(\<bbb-Z\>[\<theta\>])>.
  </remark>

  We say that <math|A,B\<in\>M<rsub|n,m>(R)> are <strong|equivalent by
  elementary operations> and write <math|A\<sim\><rsub|\<cal-E\>>B> if there
  is a sequence <math|A\<backassign\>A<rsub|0>\<rightarrow\>A<rsub|1>\<rightarrow\>\<cdots\>\<rightarrow\>A<rsub|k\<minus\>1>\<rightarrow\>A<rsub|k>\<assign\>B>
  such that <math|A<rsub|i+1>> is the result of an elementary row or column
  operation applied to <math|A<rsub|i>> for all
  <math|0\<leqslant\>i\<less\>k>.

  We say that <math|A,B\<in\>M<rsub|n,m>(R)> are <strong|equivalent> and
  write <math|A\<sim\>B> if there are matrices <math|S\<in\>GL<rsub|n>(R)>
  and <math|T\<in\>GL<rsub|m>(R)> such that <math|A=S*B*T>.

  <\observation>
    Both <math|\<sim\><rsub|\<cal-E\>>> and <math|\<sim\>> are equivalence
    relations, and in view of the definition of <math|GE<rsub|n>(R)> we have
    <math|A\<sim\><rsub|\<cal-E\>>B> if and only if there is
    <math|P,Q\<in\>GE<rsub|n>(R)> such that <math|A=P*B*Q>, so that
    <math|A\<sim\><rsub|\<cal-E\>>B> implies <math|A\<sim\>B>.
  </observation>

  <\example>
    For <math|A\<in\>M<rsub|n,m>(R)> write
    <math|r<rsub|1>,\<ldots\>,r<rsub|n>> for its rows, and
    <math|c<rsub|1>,\<ldots\>,c<rsub|m>> for its columns. For any
    <math|\<sigma\>\<in\>S<rsub|n>> we have

    <\equation*>
      <matrix|<tformat|<table|<row|<cell|r<rsub|1>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|n>>>>>>\<sim\><rsub|\<cal-E\>><matrix|<tformat|<table|<row|<cell|r<rsub|\<sigma\><around*|(|1|)>>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|\<sigma\><around*|(|n|)>>>>>>><text|
      and >(c<rsub|1>\<cdots\>c<rsub|m>)\<sim\><rsub|\<cal-E\>>(c<rsub|\<sigma\>(1)>\<cdots\>c<rsub|\<sigma\>(m)>),
    </equation*>

    since <math|\<sigma\>> is generated by transpositions, and interchanging
    rows (resp. columns) <math|i> and <math|j> corresponds to apply the
    transposition <math|(i\<nocomma\>j)> to the row (resp. column) indices.

    We say that <math|A\<in\>M<rsub|n,m>(R)> is <strong|diagonal> if
    <math|A<rsub|i,j>=0> whenever <math|i\<neq\>j>. <with|font|Segoe UI
    Emoji|\<#26A0\>>In particular, we do not insist that that <math|A> be
    square eg. <math|<matrix|<tformat|<table|<row|<cell|1>>|<row|<cell|0>>>>>,<matrix|<tformat|<table|<row|<cell|1>|<cell|0>>>>>>
    are diagonal.
  </example>

  <\example>
    If <math|A> is diagonal, interchanging rows <math|i> and <math|j> and
    columns <math|i> and <math|j> gives the matrix <math|A> with
    <math|A<rsub|i,i>> and <math|A<rsub|j,j>> interchanged. Hence for any
    <math|\<sigma\>\<in\>S<rsub|n>> we have

    <\equation*>
      A\<sim\><rsub|\<cal-E\>><matrix|<tformat|<table|<row|<cell|A<rsub|\<sigma\><around*|(|1|)>,\<sigma\><around*|(|1|)>>>|<cell|0>|<cell|\<cdots\>>>|<row|<cell|0>|<cell|A<rsub|\<sigma\><around*|(|2|)>,\<sigma\><around*|(|2|)>>>|<cell|\<ddots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>>>>>
    </equation*>

    This gives all <math|\<sigma\>> since \PAny permutation is a product of
    transpositions\Q.
  </example>

  <\example>
    Two matrices <math|A,B\<in\>M<rsub|n>(\<bbb-F\>)> are said to be
    <strong|similar> if there is <math|P\<in\>GL<rsub|n>(\<bbb-F\>)> such
    that <math|A=P<rsup|\<minus\>1>BP>, and so if <math|A> and <math|B> are
    similar then <math|A\<sim\>B>. However,

    <\equation*>
      A\<assign\><matrix|<tformat|<table|<row|<cell|0>|<cell|1>>|<row|<cell|0>|<cell|0>>>>><long-arrow|\<rubber-rightarrow\>|c<rsub|1>\<leftrightarrow\>c<rsub|2>><matrix|<tformat|<table|<row|<cell|1>|<cell|0>>|<row|<cell|0>|<cell|0>>>>>\<backassign\>B,
    </equation*>

    so that here <math|A\<sim\><rsub|\<cal-E\>>B>, but <math|B> is diagonal
    and <math|A> is not similar to a diagonal matrix <em|i.e.> it is not
    diagonalisable, so matrices can be equivalent without being similar.
  </example>

  <\theorem>
    Suppose that <math|R> is a Euclidean domain. Then every
    <math|A\<in\>M<rsub|n,m>(R)> is equivalent by elementary operations to a
    diagonal matrix.
  </theorem>

  <\proof>
    Let <math|\<cal-A\><rsub|k>> be those matrices
    <math|B\<sim\><rsub|\<cal-E\>>A> with the additional property that
    whenever <math|i\<neq\>j> and <math|min<around*|{|i,j|}>\<less\>k>, we
    have <math|B<rsub|i,j>=0>. We shall show by induction that
    <math|\<cal-A\><rsub|k>> is non-empty for <math|k\<leqslant\>min{m,n}>;
    <math|\<cal-A\><rsub|1>> contains <math|A> and so is certainly non-empty.

    Let <math|f> be a Euclidean function for <math|R>, and suppose that
    <math|\<cal-A\><rsub|k>\<neq\>\<emptyset\>> and <math|k\<less\>min{m,n}>.
    Let <math|B\<in\>\<cal-A\><rsub|k>> be a matrix with
    <math|f(B<rsub|k,k>)> minimal. First we show that
    <math|B<rsub|k,k>\<mid\>B<rsub|k,i>> for all <math|i\<gtr\>k>: if not,
    there is some <math|i\<gtr\>k> with <math|B<rsub|k,i>=q*B<rsub|k,k>+r>
    and <math|f(r)\<less\>f(B<rsub|k,k>)>, so we apply the elementary
    operations

    <\equation*>
      B=<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|8|8|cell-halign|c>|<cwith|1|-1|8|8|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|\<cdots\>>|<cell|B<rsub|k,i>>|<cell|\<cdots\>>|<cell|B<rsub|k,m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|\<cdots\>>|<cell|B<rsub|n,i>>|<cell|\<cdots\>>|<cell|B<rsub|n,m>>>>>>|)>
    </equation*>

    <\equation*>
      <long-arrow|\<rubber-rightarrow\>|c<rsub|i>\<mapsto\>c<rsub|i>-c<rsub|k>*q><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|8|8|cell-halign|c>|<cwith|1|-1|8|8|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|\<cdots\>>|<cell|B<rsub|k,i>-B<rsub|k,k>*q>|<cell|\<cdots\>>|<cell|B<rsub|k,m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|\<cdots\>>|<cell|B<rsub|n,i>-B<rsub|n,k>*q>|<cell|\<cdots\>>|<cell|B<rsub|n,m>>>>>>|)>
    </equation*>

    <\equation*>
      <long-arrow|\<rubber-rightarrow\>|c<rsub|k>\<leftrightarrow\>c<rsub|i>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|8|8|cell-halign|c>|<cwith|1|-1|8|8|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,i>-B<rsub|k,k>*q>|<cell|\<cdots\>>|<cell|B<rsub|k,k>>|<cell|\<cdots\>>|<cell|B<rsub|k,m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,i>-B<rsub|n,k>*q>|<cell|\<cdots\>>|<cell|B<rsub|n,k>>|<cell|\<cdots\>>|<cell|B<rsub|n,m>>>>>>|)>=:B<rprime|'>
    </equation*>

    Then <math|B<rprime|'>\<in\>\<cal-A\><rsub|k>> has
    <math|B<rprime|'><rsub|k,k>=B<rsub|k,i>\<minus\>q*B<rsub|k,k>=r>, but
    <math|f(B<rprime|'><rsub|k,k>)=f(r)\<less\>f(B<rsub|k,k>)> which
    contradicts the minimality in our choice of <math|B>. Similarly, but with
    row operations in place of column operations,
    <math|B<rsub|k,k>\<mid\>B<rsub|i,k>> for all <math|i\<gtr\>k>.

    For <math|k\<less\>i\<leqslant\>m> let <math|q<rsub|i>> be such that
    <math|B<rsub|k,i>=B<rsub|k,k>q<rsub|i>>. Apply elementary column
    operations

    <\equation*>
      B<long-arrow|\<rubber-rightarrow\>|c<rsub|k+1>\<mapsto\>c<rsub|k+1>-c<rsub|k>*q<rsub|k+1>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|8|8|cell-halign|c>|<cwith|1|-1|8|8|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|B<rsub|k,k+2>>|<cell|\<cdots\>>|<cell|B<rsub|k,m>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k+1,k>>|<cell|B<rsub|k+1,k+1>-B<rsub|k+1,k>*q<rsub|k+1>>|<cell|B<rsub|k+1,k+2>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|B<rsub|n,k+1>-B<rsub|n,k>*q<rsub|k+1>>|<cell|B<rsub|n,k+2>>|<cell|\<cdots\>>|<cell|B<rsub|n,m>>>>>>|)>
    </equation*>

    <\equation*>
      <with|font-base-size|10|<long-arrow|\<rubber-rightarrow\>|c<rsub|m>\<mapsto\>c<rsub|m>-c<rsub|k>*q<rsub|m>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|7|7|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|\<vdots\>>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k+1,k>>|<cell|B<rsub|k+1,k+1>-B<rsub|k+1,k>*q<rsub|k+1>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m>-B<rsub|k+1,k>*q<rsub|m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|B<rsub|n,k+1>-B<rsub|n,k>*q<rsub|k+1>>|<cell|\<cdots\>>|<cell|B<rsub|n,m>-B<rsub|n,k>*q<rsub|m>>>>>>|)>=:B<rprime|'>>
    </equation*>

    For <math|k\<less\>i\<leqslant\>n> let <math|p<rsub|i>> be such that
    <math|B<rsub|i,k>=p<rsub|i>B<rsub|k,k>>. Apply elementary row operations

    <\equation*>
      B<rprime|'><long-arrow|\<rubber-rightarrow\>|r<rsub|k+1>\<mapsto\>r<rsub|k+1>-p<rsub|k+1>*r<rsub|k>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|7|7|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|B<rsub|k+1,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m><rprime|'>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k+1,k>>|<cell|B<rsub|k+2,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|k+2,m><rprime|'>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|B<rsub|n,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|n,m><rprime|'>>>>>>|)>
    </equation*>

    <\equation*>
      <long-arrow|\<rubber-rightarrow\>|r<rsub|n>\<mapsto\>r<rsub|n>-p<rsub|n>*r<rsub|k>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|7|7|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|B<rsub|k+1,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m><rprime|'>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|B<rsub|n,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|n,m><rprime|'>>>>>>|)>=:B<rsup|\<prime\>*\<prime\>>
    </equation*>

    Then <math|B<rprime|''>\<sim\><rsub|\<cal-E\>>B<rprime|'>\<sim\><rsub|\<cal-E\>>B\<sim\><rsub|\<cal-E\>>A>
    and <math|B<rprime|''>\<in\>Ak+1>. The inductive step is complete. It
    follows that <math|\<cal-A\><rsub|min{m,n}>\<neq\>\<emptyset\>>; any
    <math|B> in this set is diagonal and equivalent to <math|A>.
  </proof>

  For <math|d<rsub|1>,\<ldots\>,d<rsub|n>\<in\>N<rsub|0>> and
  <math|B<rsub|1>\<in\>M<rsub|d<rsub|1>>(R),\<ldots\>,B<rsub|n>\<in\>M<rsub|d<rsub|n>>(R)>
  we write

  <\equation*>
    B<rsub|1>\<oplus\>\<cdots\>\<oplus\>B<rsub|n>\<assign\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1>>|<cell|0<rsub|d<rsub|1>\<times\>d<rsub|2>>>|<cell|\<cdots\>>|<cell|0<rsub|d<rsub|1>\<times\>d<rsub|n>>>>|<row|<cell|0<rsub|d<rsub|2>\<times\>d<rsub|1>>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0<rsub|d<rsub|n-1>\<times\>d<rsub|n>>>>|<row|<cell|0<rsub|d<rsub|n>\<times\>d<rsub|1>>>|<cell|\<cdots\>>|<cell|0<rsub|d<rsub|n>\<times\>d<rsub|n-1>>>|<cell|B<rsub|n>>>>>>|)>
  </equation*>

  \;

  We call the Bis the blocks of the matrix B1 \<varoplus\> \<cdots\>
  \<varoplus\> Bn, and it will be useful to allow `degenerate' 0\<times\>0
  blocks.

  <\example>
    A matrix <math|A\<in\>M<rsub|n>(R)> is diagonal with entries
    <math|d<rsub|1<rsub|>>,\<ldots\>,d<rsub|n>> if
    <math|A=(d<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>(d<rsub|n>)>. Example
    6.8. If d1+\<cdots\>+dn=n then <math|I<rsub|n>=Id<rsub|1>\<varoplus\>\<cdots\>\<varoplus\>Id<rsub|n>>.
    <with|font|Segoe UI Emoji|\<#26A0\>>This is not a special case of the
    previous example because we are allowing <math|0\<times\>0> blocks.
  </example>

  <\observation>
    If Bi \<sim\> B<rprime|'>i(resp. Bi \<sim\>E B\<prime\>i) for
    1\<leqslant\>i\<leqslant\>n then B1 \<varoplus\> \<cdots\> \<varoplus\>
    Bn \<sim\> B<rprime|'>1 \<varoplus\> \<cdots\> \<varoplus\> Bn (resp. B1
    \<varoplus\> \<cdots\> \<varoplus\> Bn \<sim\>E B<rprime|'>1 \<varoplus\>
    \<cdots\> \<varoplus\> Bn).
  </observation>

  <\lemma>
    Suppose that <math|R> is an integral domain, k \<less\> l and
    A\<in\>Mn,m(R) is diagonal with <math|\<langle\>d\<rangle\>=\<langle\>Ak,k\<rangle\>+\<langle\>Al,l\<rangle\>>
    for some <math|d\<neq\>0>, and md=Al,lAk,k. Then A is equivalent by
    elementary operations to the matrix A with Ak,k replaced by m and Al,l
    replaced by d.
  </lemma>

  <\proof>
    Let \<alpha\>, \<beta\>, p, q\<in\>R be such that
    Ak,k\<alpha\>+\<beta\>Al,l=d and Ak,k=dp, Al,l=qd, and so m=qdp. Then
  </proof>

  Acl\<mapsto\>cl+ck\<alpha\> �����\<rightarrow\>

  ...

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  Ak,k Ak,k\<alpha\>

  ...

  Al,l\ 

  ...

  \<#23A0\>

  \<#239D\>

  rk\<mapsto\>rk+\<beta\>rl �����\<rightarrow\>

  ...

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  Ak,k d

  ...

  Al,l\ 

  ...

  \<#23A0\>

  \<#239D\>

  ck\<mapsto\>ck\<minus\>clp �����\<rightarrow\>

  ...

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  0 d

  ...

  \<minus\>m Al,l\ 

  ...

  \<#23A0\>

  \<#239D\>

  rl\<mapsto\>rl\<minus\>qrk �����\<rightarrow\>

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  ...

  0 d

  ...

  \<minus\>m 0

  ...

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>
  \<#23A0\>

  rl\<leftrightarrow\>rk ���\<rightarrow\>

  \;

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  ...

  \<minus\>m

  ...

  d

  ...

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>
  \<#23A0\>

  rk\<leftrightarrow\>(\<minus\>1)rk �����\<rightarrow\>

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  ...

  m

  ...

  d

  ...

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>
  \<#23A0\>

  .

  The result is proved.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  We say that A\<in\>Mn,m(R) is in Smith normal form over R if it is diagonal
  and Ai,i \<mid\> Ai+1,i+1 for all 1\<leqslant\>i \<less\> min{n, m}.

  <\proposition>
    Suppose that R is a Bezout domain. Then every diagonal matrix
    A\<in\>Mn,m(R) is equivalent by elementary operations to a matrix in
    Smith normal form.
  </proposition>

  <\proof>
    Let Ak be the set of diagonal matrices that are elementarily equivalent
    to A, and such that if the diagonal entries are denoted a1,
    a2,\<ldots\>,amin{m,n}, then ai \<mid\> aj whenever
    1\<leqslant\>i\<leqslant\>j and i\<leqslant\>k. Certainly A\<in\>A0 since
    the hypotheses on the entries is vacuous then, so there is a maximal
    k\<in\>N\<ast\> with k\<minus\>1\<leqslant\>min{m, n} such that
    Ak\<minus\>1 is non-empty.
  </proof>

  By maximality of k for each matrix in Ak\<minus\>1 with diagonal entries
  a1, a2,\<ldots\>,amin{m,n} there is a minimal l \<gtr\> k with ak \<mid\>/
  al; let B\<in\>Ak\<minus\>1 have l maximal with this property. By Lemma
  6.10 and Proposition 3.22 we can replace ak and al by the greatest common
  divisor and least common multiple respectively of ak and al, to get a
  matrix C that is equivalent to B by elementary operations.

  Write a<rprime|'>1,\<ldots\>,a\<prime\>min{m,n}for the diagonal entries of
  C, so that for i \<in\>/ {k,l} we have a<rprime|'>i= ai. a<rprime|'>kand
  a<rprime|'>lare linear combinations of ak and al and so for i\<leqslant\>k
  \<minus\>1, a<rprime|'>idivides them both, and hence for
  1\<leqslant\>i\<leqslant\>j we have we have a<rprime|'>i\<mid\>
  a<rprime|'>j. It follows that C\<in\>Ak\<minus\>1. Finally
  a<rprime|'>k\<mid\> ak and so

  a<rprime|'>k\<mid\> a\<prime\>jfor k\<leqslant\>j \<less\> l, but also
  a<rprime|'>k\<mid\> a<rprime|'>lcontradicting maximality of l. The result
  is proved.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  <\theorem>
    Suppose that R is a Euclidean domain. Then every A\<in\>Mn,m(R) is equiv
    alent by elementary operations to a matrix in Smith normal form.
  </theorem>

  <\proof>
    This follows from Theorem 6.6 and Proposition 6.11.
  </proof>

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  <\remark>
    Following the work of Kaplanksy [Kap49] an integral domain R for which
    every A\<in\>Mn,m(R) is equivalent to a matrix in Smith normal form, is
    called an elementary divisor domain, so in this language Theorem 6.12
    shows that every Euclidean domain is an elementary divisor domain.
  </remark>

  Every finitely generated ideal in an elementary divisor domain is principal
  [LLS74, The orem 3.1], and it is an open problem [Lor12] (going back at
  least to [Hel43]) to decide which Bezout domains are elementary divisor
  rings.

  \;

  7 Applications of Smith normal form

  With these tools we are in a position to describe the structure of finitely
  generated modules over a Euclidean domain:

  <\theorem>
    Suppose that R is a Euclidean domain and M is generated by
    x1,\<ldots\>,xn. Then there are elements a1 \<mid\> a2 \<mid\> \<cdots\>
    \<mid\> an in R and a matrix Q\<in\>GLn(R) such that
  </theorem>

  (R/\<langle\>a1\<rangle\>) \<varoplus\> \<cdots\> \<varoplus\>
  (R/\<langle\>an\<rangle\>)\<rightarrow\>M

  (r1+\<langle\>a1\<rangle\>,\<ldots\>,rn+\<langle\>an\<rangle\>)\<mapsto\>(rQ).x1+\<cdots\>+(rQ).xn\ 

  is a well-defined R-linear isomorphism.

  <\proof>
    The map
  </proof>

  \<Phi\>x:Rn\<rightarrow\>M; r\<mapsto\>r1.x1+\<cdots\>+rn.xn\ 

  is an R-linear surjection. Since R is a Euclidean domain it is a PID and
  hence by Proposition 5.29 there is A\<in\>Mn(R) such that the kernel of
  this map is RnA. By Theorem 6.12 there is a diagonal matrix B\<in\>Mn(R)
  with entries a1 \<mid\> \<cdot\> \<cdot\> \<cdot\> \<mid\> an and P,
  Q\<in\>GLn(R) such that A=P BQ. The map

  Rn\<rightarrow\>M; r\<mapsto\>(rQ).x1+\<cdots\>+(rQ).xn\ 

  is an R-linear map which is surjective because Q is invertible and \<Phi\>x
  is surjective. The kernel is the set of r\<in\>Rn for which rQ\<in\>ker
  \<Phi\>x i.e. for which there is r<rprime|'>\<in\>Rn such that
  rQ=r\<prime\>A. This is true if and only if r=(r<rprime|'>P)(P
  \<minus\>1AQ)=(r<rprime|'>P)B. Since P is invertible r is in the kernel if
  and only if r\<in\>RnB=\<langle\>a1\<rangle\> \<varoplus\> \<cdots\>
  \<varoplus\> \<langle\>an\<rangle\>. Finally, the composition of maps

  (R/\<langle\>a1\<rangle\>) \<varoplus\> \<cdots\> \<varoplus\>
  (R/\<langle\>an\<rangle\>)\<rightarrow\>Rn/RnB\<rightarrow\>M

  (r1+\<langle\>a1\<rangle\>,\<ldots\>,rn+\<langle\>an\<rangle\>)\<mapsto\>r+\<langle\>a1\<rangle\>
  \<varoplus\> \<cdots\> \<varoplus\> \<langle\>an\<rangle\>\<mapsto\>(rQ).x1+\<cdots\>+(rQ).xn
  is a composition of well-defined R-linear isomorphisms by the First
  Isomorphism Theorem.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  This in turn lets us describe the structure of finitely generated
  commutative groups:

  Corollary 7.2. Suppose that G is a commutative group generated by
  x1,\<ldots\>,xn. Then there are natural numbers d1 \<mid\> d2 \<mid\>
  \<cdots\> \<mid\> dn (which may be 0) such that G is isomorphic to
  Z/\<langle\>d1\<rangle\> \<varoplus\> \<cdots\> \<varoplus\>
  Z/\<langle\>dn\<rangle\>.

  <\proof>
    This is a corollary of Theorem 7.1 since a commutative group is a
    Z-module, and Z is a Euclidean domain. We may ensure the dis are natural
    numbers by multiplying by a
  </proof>

  unit in Z as necessary.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  \;

  <subsection|Matrix forms>

  In this section we work with matrices multiplying columns on the left
  rather than rows on the right. Equivalent matrices induce isomorphisms in
  the same way as in the proof of Theorem 7.1:

  <\proposition>
    Suppose that A, B\<in\>Mn(F[X]), and P, Q\<in\>GLn(F[X]) are such that
    A=P BQ. Then the map
  </proposition>

  F[X]ncol/AF[X]ncol\<rightarrow\>F[X]ncol/BF[X]mcol; x+AF[X]ncol\<mapsto\>xP
  \<minus\>1+BF[X]ncol is a well-defined F[X]-linear isomorphism.

  <\proof>
    Since F[X] is commutative BF[X]ncol is an F[X]-module, and hence
    F[X]ncol\<rightarrow\>F[X]ncol/BF[X]ncol; x\<mapsto\>P
    \<minus\>1x+BF[X]ncol is a well-defined F[X]-linear surjection. It has
    kernel AF[X]ncol, since P \<minus\>1x\<in\>BF[X]ncol if and only if P
    \<minus\>1x=Bx<rprime|'>for some x<rprime|'>\<in\>F[X]ncol, but P
    \<minus\>1x=Bx<rprime|'>if and only if x=(P
    BQ)(Q\<minus\>1x<rprime|'>)=A(Q\<minus\>1x<rprime|'>), and hence P
    \<minus\>1x\<in\>BF[X]ncol if and only if x=Ax<rprime|''> for some
    x<rprime|''>\<in\>F[X]ncol since Q is invertible. The result then follows
    by the First Isomorphism Theorem.
  </proof>

  For p=a0+\<cdots\> +adXd\<in\>F[X] and C\<in\>Mn(F[X]) write p.C for the
  matrix with (p.C)i,j=p(X)Ci,j(X) \U the . is the scalar multiplication in
  the F[X]-module Mn(F[X]) \U and write p(C) the evaluation homomorphism at C
  extending the ring homomorphism F\<rightarrow\>Mn(F[X]), which is a
  composition of the inclusion homomorphism F\<rightarrow\>F[X] and the
  diagonal homomorphism F[X]\<rightarrow\>Mn(F[X]) i.e.

  p(C)=a0.In+\<cdots\>+ad.Cd.

  <\lemma>
    Suppose that A\<in\>Mn(F). Then et1+(X.In\<minus\>A)F[X]ncol,\<ldots\>,etn+(X.In\<minus\>A)F[X]ncol
    is a basis of the F-vector space F[X]ncol/(X.In\<minus\>A)F[X]ncol.
  </lemma>

  <\proof>
    Since the matrix X.In is in the centre of Mn(F[X]),

    (X.In)i\<minus\>Ai=(X.In\<minus\>A)((X.In)i\<minus\>1+\<cdots\>+Ai\<minus\>1);

    and since F[X] is commutative, left multiplication in Mn(F[X]) is
    F[X]-linear, so

    p(X.In)\<minus\>p(A)=(X.In\<minus\>A)

    d

    \<big-sum\> i=1

    ai.(Ai\<minus\>1+\<cdots\>+(X.In)i\<minus\>1)=(X.In\<minus\>A)Q

    for some Q\<in\>Mn(F[X]). Now, the map

    \<Phi\>:F[X]ncol\<rightarrow\>Fncol; p\<mapsto\>p1(A)et1+\<cdots\>+pn(A)etn

    is F-linear, and to identify its kernel we use the same method of proof
    as for the Factor Theorem: Specifically, for p\<in\>ker \<Phi\> we have

    p=p\<minus\>\<Phi\>(p)=(p1(X.In)\<minus\>p1(A))et1+\<cdots\>+(pn(X.In)\<minus\>pn(A))etn=(X.In
    \<minus\>A)(Q1et1+\<cdots\>+Qnetn),

    for Q1,\<ldots\>,Qn\<in\>Mn(F[X]). In particular,
    p\<in\>(X.In\<minus\>A)F[X]ncol. In the other direction, note that if
    p\<in\>(X.In\<minus\>A)F[X]ncol is not identically 0 then there is i such
    that deg pi \<gtr\> 0. It follows that
    et1+(X.In\<minus\>A)F[X]ncol,\<ldots\>,etn+(X.In\<minus\>A)F[X]ncol is
    F-linearly independent as a subset of the subspace
    F[X]ncol/(X.In\<minus\>A)F[X]ncol, but they are also spanning since
    \<Phi\>(eti)=etifor all 1\<leqslant\>i\<leqslant\>n, and
    et1,\<ldots\>,etnis a spanning subset of Fncol. The result is

    proved.

    <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>
  </proof>

  <\proposition>
    Suppose that <math|A,B\<in\>M<rsub|n>(\<bbb-F\>)>. Then X.In\<minus\>A
    and X.In\<minus\>B are equivalent as matrices in
    <math|M<rsub|n>(\<bbb-F\>[X])> if and only if <math|A> and <math|B> are
    similar as matrices in <math|M<rsub|n>(\<bbb-F\>)>.
  </proposition>

  <\proof>
    If A and B are similar then there is P\<in\>GLn(F) such that A=P BP
    \<minus\>1, but then X.In \<minus\>A=P(X.In \<minus\>B)P \<minus\>1 and
    X.In \<minus\>A is similar, and so equivalent, to X.In \<minus\>B as
    matrices in Mn(F[X]).
  </proof>

  In the other direction, since X.In\<minus\>A \<sim\> X.In\<minus\>B,
  Proposition 7.3 gives an F[X]-linear isomorphism

  \<Phi\>:F[X]ncol/(X.In\<minus\>A)F[X]ncol\<rightarrow\>F[X]ncol/(X.In\<minus\>B)F[X]ncol.

  By Lemma 7.4 we know et1 +(X.In \<minus\>A)F[X]ncol,\<ldots\>,etn +(X.In
  \<minus\>A)F[X]ncol is an F-basis for F[X]ncol/(X.In\<minus\>A)F[X]ncol,
  and similarly with A replaced by B. Since \<Phi\> is, in particular, an
  F-linear bijection we conclude that there is P\<in\>GLn(F) such that

  \<Phi\>(v+(X.In\<minus\>A)F[X]ncol)=P v+(X.In\<minus\>B)F[X]ncol for all
  v\<in\>Fncol.

  Now, \<Phi\> is F[X]-linear, so for v\<in\>Fncol we have

  0=\<Phi\>((X.In\<minus\>A)v+(X.In\<minus\>A)F[X]ncol)

  = X\<Phi\>(v+(X.In\<minus\>A)F[X]ncol)\<minus\>\<Phi\>(Av+(X.In\<minus\>A)F[X]ncol)

  = XP v\<minus\>P Av+(X.In\<minus\>B)F[X]ncol.

  In other words, XP v\<minus\>P Av=Xw\<minus\>Bw for some w\<in\>F[X]ncol.
  Equating coefficients we have w=P v and P Av=Bw, and hence Av=P
  \<minus\>1BP v. Since v was arbitrary we have that

  A=P \<minus\>1BP as claimed.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  Given a monic polynomial f(X)=Xd+ad\<minus\>1Xd\<minus\>1+\<cdots\>+a0\<in\>F[X]\<ast\>
  we define the d\<times\>d

  matrices

  C(f) \<#2236\>=

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  0 \<cdots\> \<cdots\> 0 \<minus\>a0 1......... 0............ ......... 0...
  0 \<cdots\> 0 1 \<minus\>ad\<minus\>1\ 

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>
  \<#23A0\>

  and D(f) \<#2236\>=

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  f(X) 0 \<cdots\> 0 0 1...... ......... 0 0 \<cdots\> 0 1

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>
  \<#23A0\>

  .

  The matrix C(f) is called the companion matrix to <math|f>.
  <with|font|Segoe UI Emoji|\<#26A0\>>We allow d=0 when these are `empty'
  0\<times\>0 matrices.

  <\example>
    For f(X)\<in\>F[X]\<ast\> we have X.Id\<minus\>C(f) \<sim\>E D(f). To see
    this write f(X)=Xd+ad\<minus\>1Xd\<minus\>1+\<cdots\>+a0, and put f0(X)=1
    and fi=Xfi\<minus\>1(X)+ad\<minus\>ifor 1\<leqslant\>i\<leqslant\>d so
    that f1(X)=X+ad\<minus\>1 and fd(X)=f(X); and apply row and column
    operations in four groups:
  </example>

  X.Id\<minus\>C(f) =

  X 0 \<cdots\> 0 a0\ 

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  \<minus\>1............

  0...... 0...

  ......... X ad\<minus\>2\ 

  \<#239D\>

  \<#23A0\>

  0 \<cdots\> 0 \<minus\>1 X+ad\<minus\>1\ 

  rd\<minus\>1\<mapsto\>rd\<minus\>1+Xrd ...

  r1\<mapsto\>r1+Xr2 ���������\<rightarrow\>

  0 0 \<cdots\> 0 fd(X) \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  \<minus\>1............

  0...... 0...

  ......... 0 f2(X) \<#239D\>

  \<#23A0\>

  0 \<cdots\> 0 \<minus\>1 f1(X)

  cd\<mapsto\>cd+f1(X)cd\<minus\>1\ 

  ...

  cd\<mapsto\>cd+fd\<minus\>1(X)c1 ������������\<rightarrow\>

  0 0 \<cdots\> 0 fd(X) \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  \<minus\>1......... 0 0...... 0...

  ......... 0 0

  \<#239D\>

  \<#23A0\>

  0 \<cdots\> 0 \<minus\>1 0

  c1\<leftrightarrow\>cd\ 

  ...cd\<minus\>1\<leftrightarrow\>cd �������\<rightarrow\>

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  fd(X) 0 \<cdots\> 0 0 \<minus\>1...... ......... 0 0 \<cdots\> 0 \<minus\>1

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  c2\<leftrightarrow\>(\<minus\>1)c2\ 

  ...

  cd\<leftrightarrow\>(\<minus\>1)cd ��������\<rightarrow\>
  D(fd)=D(f). \<#23A0\>

  <with|font|Segoe UI Emoji|\<#26A0\>>The order of the row operations in the
  first group and the column operations in the third group matter, so we do
  rd\<minus\>1\<mapsto\>rd\<minus\>1+Xrd first and r1\<mapsto\>r1+Xr2 last in
  the first group, and cd\<mapsto\>cd+f1(X)cd\<minus\>1 first and
  cd\<mapsto\>cd+fd\<minus\>1(X)c1 last in the third group; in the other two
  groups the operations commute.

  For <math|\<lambda\>\<in\>\<bbb-F\>> and <math|d\<in\>\<bbb-N\><rsub|0>>
  define the <math|d>-dimensional Jordan matrix with eigenvalue \<lambda\> to
  be the (possibly empty) <math|d\<times\>d>-matrix

  J(\<lambda\>, d) \<#2236\>=

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>
  \<#239D\>

  \<lambda\> 1 0 \<cdots\> 0 0 \<lambda\>......... ............ 0 ......
  \<lambda\> 1 0 \<cdots\> \<cdots\> 0 \<lambda\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  ; and recall D((X\<minus\>\<lambda\>)d) =

  \<#239D\>

  \<#23A0\>

  (X\<minus\>\<lambda\>)d 0 \<cdots\> 0 0 1...... ......... 0 0 \<cdots\> 0 1

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>
  \<#23A0\>

  .

  <\example>
    For \<lambda\>\<in\>F we have X.Id\<minus\>J(\<lambda\>, d) \<sim\>E
    D((X\<minus\>\<lambda\>)d). To see this note that
    X.Id\<minus\>J(\<lambda\>, d) equals
  </example>

  X\<minus\>\<lambda\> \<minus\>1 0 \<cdots\> 0
  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  0 X\<minus\>\<lambda\>......... ............ 0

  ...... X\<minus\>\<lambda\> \<minus\>1 \<#239D\>

  \<#23A0\>

  0 \<cdots\> \<cdots\> 0 X\<minus\>\<lambda\>

  cd\<minus\>1\<mapsto\>cd\<minus\>1+(X\<minus\>\<lambda\>)cd ...

  c1\<mapsto\>c1+(X\<minus\>\<lambda\>)c2
  �����������\<rightarrow\>

  0 \<minus\>1 0 \<cdots\> 0

  \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  0 0.........

  ............ 0

  ...... 0 \<minus\>1

  \<#239D\>

  \<#23A0\>

  (X\<minus\>\<lambda\>)d \<cdots\> \<cdots\> 0 0

  r1\<leftrightarrow\>rd\ 

  ...rd\<minus\>1\<leftrightarrow\>rd �������\<rightarrow\>

  (X\<minus\>\<lambda\>)d 0 \<cdots\> 0 \<#239B\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>\<#239C\>

  \<#239E\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>\<#239F\>

  0 \<minus\>1......

  ......... 0

  \<#239D\>

  \<#23A0\>

  0 \<cdots\> 0 \<minus\>1

  c2\<leftrightarrow\>(\<minus\>1)c2\ 

  ...

  cd\<leftrightarrow\>(\<minus\>1)cd ��������\<rightarrow\>
  D((X\<minus\>\<lambda\>)d)

  <\theorem>
    Suppose that A\<in\>Mn(F). Then there are monic polynomials f1 \<mid\>
    \<cdots\> \<mid\> fn such that A \<sim\>E C(f1) \<varoplus\> \<cdots\>
    \<varoplus\> C(fn).
  </theorem>

  <\proof>
    By Theorem 6.12 there are polynomials f1 \<mid\> \<cdots\> \<mid\> fn
    such that X.In\<minus\>A \<sim\>E \<#2206\>(X) where \<#2206\>(X) is the
    diagonal matrix with entries f1,\<ldots\>,fn. In particular, there are P,
    Q\<in\>GLn(F[X]) such that P(X)(X.In \<minus\>A)Q(X)=\<#2206\>(X). Since
    P(X) and Q(X) are invertible we have detP(X) detP(X)\<minus\>1=1 and
    hence detP(X), detQ(X)\<in\>U(R) (see Exercise IV.7 for the proof that
    determinant is multiplicative), hence det(X.In\<minus\>A) are associates
    det \<#2206\>(X) in F[X]. In particular, since det(X.In\<minus\>A) is
    monic and of degree n, none of f1,\<ldots\>,fn is identically 0 and so
    they all have degrees which we denote d1,\<ldots\>,dn respectively and
    satisfy n=d1 +\<cdots\> +dn. Moreover, by multiplying by units we may
    assume that f1,\<ldots\>,fn are monic.
  </proof>

  By permuting columns and rows as necessary we have \<#2206\>(X) \<sim\>E
  D(f1)\<varoplus\>\<cdots\>\<varoplus\>D(fn). The calculation in Example 7.6
  shows us that D(fi) \<sim\>E X.Idi\<minus\>C(fi) and hence X.In\<minus\>A
  \<sim\>E\ 

  X.In\<minus\>C(f1) \<varoplus\> \<cdots\> \<varoplus\> C(fn). The result
  now follows from Proposition 7.5.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  \;

  \;

  A matrix is said to be in rational canonical form if it is a block diagonal
  matrix with blocks C(f1),\<ldots\>,C(fn) for monic polynomials f1 \<mid\>
  \<cdots\> \<mid\> fn. In particular, the above says that every matrix is
  similar to a matrix in rational canonical form.

  \;

  <\remark>
    Although we shall not prove it, if two matrices in rational canonical
    form are similar then they are equal.
  </remark>

  <\example>
    For f(X)=(X\<minus\>\<lambda\>1)d1\<cdots\>(X\<minus\>\<lambda\>n)dn with
    \<lambda\>1,\<ldots\>,\<lambda\>n pairwise distinct and
    d1+\<cdots\>+dn=n, we have
  </example>

  D(f) \<sim\>E D((X\<minus\>\<lambda\>1)d1 ) \<varoplus\> \<cdots\>
  \<varoplus\> D((X\<minus\>\<lambda\>n)dn ).

  To see this, we use induction on r to show that

  D((X\<minus\>\<lambda\>1)d1 ) \<varoplus\> \<cdots\> \<varoplus\>
  D((X\<minus\>\<lambda\>n)dn ) \<sim\>E D(fr) \<varoplus\>
  D((X\<minus\>\<lambda\>r+1)dr+1 ) \<varoplus\> \<cdots\> \<varoplus\>
  D((X\<minus\>\<lambda\>n)dn )

  where fr(X)=(X\<minus\>\<lambda\>r)dr fr\<minus\>1(X) and f0(X)=1. This is
  certainly true when r=0, and for the inductive step when <math|r\<less\>n>
  note that the ideal generated by fr and (X\<minus\>\<lambda\>r+1)dr+1 is
  principal, say generated by gr. If gr has a root then it is a root of
  (X\<minus\>\<lambda\>r+1)dr+1 and also of fr, hence gr has no root and
  \<langle\>fr\<rangle\>+\<langle\>(X\<minus\>\<lambda\>r+1)dr+1
  \<rangle\>=\<langle\>1\<rangle\>. By Lemma 6.10 we can replace the first
  element on the diagonal \U that is fr \U by
  fr(X\<minus\>\<lambda\>r+1)dr+1=fr+1, and the (deg fr+1)st element on the
  diagonal \U that is (X\<minus\>\<lambda\>r+1)dr+1 by 1. The resulting
  matrix has (deg fr)\<minus\>1+dr+1=(deg fr+1)\<minus\>1 copies of 1 on the
  diagonal after the initial fr+1, and hence equals D(fr+1) \<varoplus\>
  D((X\<minus\>\<lambda\>r+1)dr+1 ) \<varoplus\> \<cdots\> \<varoplus\>
  D((X\<minus\>\<lambda\>n)dn ). The example is complete.

  <\theorem>
    Suppose that A\<in\>Mn(C). Then there are
    \<lambda\>1,\<ldots\>,\<lambda\>n\<in\>C and t1,\<ldots\>,tn\<in\>N0 with
    t1+\<cdots\>+tn=n such that A \<sim\>E J(\<lambda\>1, t1) \<varoplus\>
    \<cdots\> \<varoplus\> J(\<lambda\>n, tn).
  </theorem>

  <\proof>
    By Theorem 6.6 there are polynomials f1,\<ldots\>,fn such that
    X.In\<minus\>A \<sim\>E \<#2206\>(X) where \<#2206\>(X) is the diagonal
    matrix with entries f1,\<ldots\>,fn. As in the proof of Theorem 7.8 we
    conclude that we may suppose each fiis monic and write difor its degree,
    and n=d1+\<cdots\>+dn. By permuting columns and rows as necessary we have
    \<#2206\>(X) \<sim\>E D(f1) \<varoplus\> \<cdots\> \<varoplus\> D(fn).
  </proof>

  If f\<in\>C[X] is irreducible then f(X) \<sim\> X\<minus\>\<lambda\> for
  some \<lambda\>\<in\>C \U this is where we use the fact that the field is
  the complex numbers rather than a more general field \U so since C[X] is a
  Factorisation domain, we conclude that fi(X)=(X
  \<minus\>\<lambda\>i,1)di,1\<cdots\>(X \<minus\>\<lambda\>i,ri)di,ri with
  \<lambda\>i,1,\<ldots\>,\<lambda\>i,ri pairwise distinct and
  di,1+\<cdots\>+di,ri=di. In view of the calculation in Examples 7.7 & 7.10
  we have

  D(fi) \<sim\>E D((X\<minus\>\<lambda\>i,1)di,1 ) \<varoplus\> \<cdots\>
  \<varoplus\> D((X\<minus\>\<lambda\>i,ri)di,ri )

  \<sim\>E (X.Idi,1\<minus\>J(\<lambda\>i,1, di,1)) \<varoplus\> \<cdots\>
  \<varoplus\> (X.Idi,ri\<minus\> J(\<lambda\>i,ri, di,ri)).

  Finally, let \<lambda\>1,\<ldots\>,\<lambda\>n be
  \<lambda\>1,1,\<ldots\>,\<lambda\>1,r1,
  \<lambda\>2,1,\<ldots\>,\<lambda\>2,r2,\<ldots\>,\<lambda\>n,1,\<ldots\>,\<lambda\>n,rnin
  order and similarly

  for t1,\<ldots\>,tn. The result is proved by Proposition 7.5.

  <tabular|<tformat|<twith|table-hmode|min>|<twith|table-width|1par>|<cwith|1|-1|1|-1|cell-hyphen|t>|<table|<row|<cell|>>>>>

  A matrix is said to be in Jordan normal form if it is a block diagonal
  matrix with blocks J(\<lambda\>1, d1),\<ldots\>,J(\<lambda\>n, dn) for
  \<lambda\>1,\<ldots\>,\<lambda\>n\<in\>F and d1,\<ldots\>,dn\<in\>N0. In
  particular, the above theorem says that every matrix over C is similar to a
  matrix in Jordan normal form.

  \;

  References

  [Ber14] D. Berlyne. Ideal theory in rings (Translation of \PIdealtheorie in
  Ringbereichen\Q by Emmy Noether). 2014, arXiv:1401.2577.

  [CNT19] C. J. Conidis, P. P. Nielsen, and V. Tombs. Transfinitely valued
  euclidean domains have arbitrary indecomposable order type. Communications
  in Algebra, 47(3):1105\U1113, 2019. doi:10.1080/00927872.2018.1501569.

  [Coh66] P. M. Cohn. On the structure of the GL2 of a ring. Inst. Hautes
  Etudes Sci. \A Publ. Math., (30):5\U53, 1966. URL

  http://www.numdam.org/item?id=PMIHES_1966__30__5_0.

  [Con] K. Conrad. Remarks about Euclidean domains. URL

  https://kconrad.math.uconn.edu/blurbs/ringtheory/euclideanrk.pdf.

  [Fuc58] L. Fuchs. Abelian groups. Publishing House of the Hungarian Academy
  of Sciences, Budapest, 1958.

  [Gra74] A. Grams. Atomic rings and the ascending chain condition for
  principal ideals. Proc. Cambridge Philos. Soc., 75:321\U329, 1974.
  doi:10.1017/s0305004100048532.

  [Hel43] O. Helmer. The elementary divisor theorem for certain rings without
  chain condition. Bull. Amer. Math. Soc., 49(4):225\U236, 04 1943. URL

  https://projecteuclid.org:443/euclid.bams/1183505099.

  [Kap49] I. Kaplansky. Elementary divisors and modules. Trans. Amer. Math.
  Soc., 66:464\U491, 1949. doi:10.2307/1990591.

  [Kap70] I. Kaplansky. Commutative rings. Allyn and Bacon, Inc., Boston,
  Mass., 1970.

  [Kea98] M. E. Keating. A First Course in Module Theory. Imperial College
  Press, 1998. doi:https://doi.org/10.1142/p082.

  [Lam07] T. Y. Lam. Exercises in modules and rings. Problem Books in
  Mathematics. Springer, New York, 2007. doi:10.1007/978-0-387-48899-8.

  [Lan02] S. Lang. Algebra, volume 211 of Graduate Texts in Mathematics.
  Springer-Verlag, New York, third edition, 2002.
  doi:10.1007/978-1-4613-0041-0.

  [LLS74] M. D. Larsen, W. J. Lewis, and T. S. Shores. Elementary divisor
  rings and finitely presented modules. Transactions of the American
  Mathematical Society, 187:231\U248, 1974. doi:10.2307/1997051.

  [Lor12] D. Lorenzini. Elementary divisor domains and B\Aezout domains. J.
  Algebra, 371:609\U619, 2012. doi:10.1016/j.jalgebra.2012.08.020.

  [Noe21] E. Noether. Idealtheorie in Ringbereichen. Math. Ann.,
  83(1-2):24\U66, 1921. doi:10.1007/BF01464225.

  [Poo19] B. Poonen. Why all rings should have a 1. Math. Mag., 92(1):58\U62,
  2019. doi:10.1080/0025570X.2018.1538714.

  [She88] K. Shen. The historical development of the Chinese remainder
  theorem. J. Hangzhou Univ. Natur. Sci. Ed., 15(3):270\U282, 1988.

  [Sou20] K. Soundararajan. Bertrand's postulate and the existence of finite
  fields. 2020, arXiv:2007.01389.

  [Tol04] J. R. R. Tolkein. The Fellowship of the Ring. The Lord of the Rings
  Part I. HarperCollins e-books, 50th anniversary edition, 2004. URL

  https://s3.amazonaws.com/scschoolfiles/112/

  j-r-r-tolkien-lord-of-the-rings-01-the-fellowship-of-the-ring-retail-pdf.
  pdf.
</body>

<\initial>
  <\collection>
    <associate|font-base-size|11>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|4|?>>
    <associate|auto-10|<tuple|6|?>>
    <associate|auto-11|<tuple|6.1|?>>
    <associate|auto-12|<tuple|6.2|?>>
    <associate|auto-13|<tuple|6.3|?>>
    <associate|auto-14|<tuple|6.4|?>>
    <associate|auto-2|<tuple|4.1|?>>
    <associate|auto-3|<tuple|4.2|?>>
    <associate|auto-4|<tuple|4.3|?>>
    <associate|auto-5|<tuple|5|?>>
    <associate|auto-6|<tuple|5.1|?>>
    <associate|auto-7|<tuple|5.2|?>>
    <associate|auto-8|<tuple|5.3|?>>
    <associate|auto-9|<tuple|5.4|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Modules:
      an introduction> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1tab>|4.1<space|2spc>Linear maps
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1tab>|4.2<space|2spc>Isomorphisms and submodules
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1tab>|4.3<space|2spc>Quotients and the First
      Isomorphism Theorem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Free
      modules> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>

      <with|par-left|<quote|1tab>|5.1<space|2spc>Generation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1tab>|5.2<space|2spc>Linear independence
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1tab>|5.3<space|2spc>Bases
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1tab>|5.4<space|2spc>Presentations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Elementary
      operations and the Smith normal form>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10><vspace|0.5fn>

      <with|par-left|<quote|1tab>|6.1<space|2spc>Transvections
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1tab>|6.2<space|2spc>Dilations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1tab>|6.3<space|2spc>Interchanges
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1tab>|6.4<space|2spc>Matrix forms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>
    </associate>
  </collection>
</auxiliary>