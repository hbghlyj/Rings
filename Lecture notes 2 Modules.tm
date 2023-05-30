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
    elements of <math|R<rsup|n>> with <math|1<rsub|R>> in the <math|i>th
    position and <math|0<rsub|R>> elsewhere. Similarly write
    <math|e<rsup|t><rsub|i>> for the column vector in
    <math|R<rsup|n><rsub|<text|col>>> with <math|1<rsub|R>> in the <math|i>th
    row and <math|0<rsub|R>>s elsewhere.

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
    S<rsub|i>\<subset\>\<cal-E\>>, and a finite union of finite sets is
    finite as required.
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

    For the last part \PSuppose <math|M> is finitely generated, then <math|M>
    has a finite basis\Q: Let <math|\<cal-E\>> be a basis for <math|M>, then
    <math|\<cal-E\>> is minimal generating set by the first part, and
    <math|\<cal-E\>> contains a finite generating set
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
  replaced by the <math|i>th column times <math|u> and as above we write this
  and the corresponding row operation as

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
    <math|\<sigma\>\<in\>S<rsub|n>> and <math|\<tau\>\<in\>S<rsub|m>> we have

    <\equation*>
      <matrix|<tformat|<table|<row|<cell|r<rsub|1>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|n>>>>>>\<sim\><rsub|\<cal-E\>><matrix|<tformat|<table|<row|<cell|r<rsub|\<sigma\><around*|(|1|)>>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|\<sigma\><around*|(|n|)>>>>>>><text|
      and ><matrix|<tformat|<table|<row|<cell|c<rsub|1>>|<cell|\<cdots\>>|<cell|c<rsub|m>>>>>>\<sim\><rsub|\<cal-E\>><matrix|<tformat|<table|<row|<cell|c<rsub|\<tau\><around*|(|1|)>>>|<cell|\<cdots\>>|<cell|c<rsub|\<tau\><around*|(|m|)>>>>>>>,
    </equation*>

    since <math|\<sigma\>> (resp. <math|\<tau\>>) is generated by
    transpositions, and interchanging rows (resp. columns) <math|i> and
    <math|j> corresponds to apply the transposition <math|(i\<nocomma\>j)> to
    the row (resp. column) indices.
  </example>

  We say that <math|A\<in\>M<rsub|n,m>(R)> is <strong|diagonal> if
  <math|A<rsub|i,j>=0> whenever <math|i\<neq\>j>. <with|font|Segoe UI
  Emoji|\<#26A0\>>In particular, we do <em|not> insist that <math|A> be
  square eg. <math|<matrix|<tformat|<table|<row|<cell|1>>|<row|<cell|0>>>>>,<matrix|<tformat|<table|<row|<cell|1>|<cell|0>>>>>>
  are diagonal.

  <\example>
    If <math|A\<in\>M<rsub|n,m><around*|(|R|)>> is diagonal, interchanging
    rows <math|i> and <math|j> and columns <math|i> and <math|j> gives the
    matrix <math|A> with <math|A<rsub|i,i>> and <math|A<rsub|j,j>>
    interchanged. Hence for any <math|\<sigma\>\<in\>S<rsub|min<around*|{|n,m|}>>>
    we have

    <\equation*>
      A\<sim\><rsub|\<cal-E\>><matrix|<tformat|<table|<row|<cell|A<rsub|\<sigma\><around*|(|1|)>,\<sigma\><around*|(|1|)>>>|<cell|0>|<cell|\<cdots\>>>|<row|<cell|0>|<cell|A<rsub|\<sigma\><around*|(|2|)>,\<sigma\><around*|(|2|)>>>|<cell|\<ddots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>>>>>
    </equation*>
  </example>

  <\example>
    Two matrices <math|A,B\<in\>M<rsub|n>(\<bbb-F\>)> are said to be
    <strong|similar> if there is <math|P\<in\>GL<rsub|n>(\<bbb-F\>)> such
    that <math|A=P<rsup|\<minus\>1>B*P>, and so if <math|A> and <math|B> are
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
    diagonal matrix. [This is weaker than \<#2018\>every symmetric real
    matrix is similar to diagonal matrix' in linear algebra, because matrices
    can be equivalent without being similar.]
  </theorem>

  <\proof>
    Let <math|\<cal-A\><rsub|k>> be those matrices
    <math|B\<sim\><rsub|\<cal-E\>>A> with the additional property that
    whenever <math|i\<neq\>j> and <math|min<around*|{|i,j|}>\<less\>k>, we
    have <math|B<rsub|i,j>=0>. We shall show by induction that
    <math|\<cal-A\><rsub|k>> is non-empty for <math|k\<leqslant\>min{m,n}+1>;
    <math|\<cal-A\><rsub|1>> contains <math|A> and so is certainly non-empty.

    Let <math|f> be a Euclidean function for <math|R>, and suppose that
    <math|\<cal-A\><rsub|k>\<neq\>\<emptyset\>> and <math|k\<less\>min{m,n}>.
    Let <math|B\<in\>\<cal-A\><rsub|k>> be a matrix with
    <math|f(B<rsub|k,k>)> minimal. First we show that
    <math|B<rsub|k,k>\<divides\>B<rsub|k,i>> for all <math|i\<gtr\>k>: if
    not, there is some <math|i\<gtr\>k> with
    <math|B<rsub|k,i>=q*B<rsub|k,k>+r> and <math|f(r)\<less\>f(B<rsub|k,k>)>,
    so we apply the elementary operations

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
    <math|B<rsub|k,k>\<divides\>B<rsub|i,k>> for all <math|i\<gtr\>k>.

    For <math|k\<less\>i\<leqslant\>m> let <math|q<rsub|i>> be such that
    <math|B<rsub|k,i>=B<rsub|k,k>q<rsub|i>>. Apply elementary column
    operations

    <\equation*>
      B<long-arrow|\<rubber-rightarrow\>|c<rsub|k+1>\<mapsto\>c<rsub|k+1>-c<rsub|k>*q<rsub|k+1>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|8|8|cell-halign|c>|<cwith|1|-1|8|8|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|B<rsub|k,k+2>>|<cell|\<cdots\>>|<cell|B<rsub|k,m>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k+1,k>>|<cell|B<rsub|k+1,k+1>-B<rsub|k+1,k>*q<rsub|k+1>>|<cell|B<rsub|k+1,k+2>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|B<rsub|n,k+1>-B<rsub|n,k>*q<rsub|k+1>>|<cell|B<rsub|n,k+2>>|<cell|\<cdots\>>|<cell|B<rsub|n,m>>>>>>|)>
    </equation*>

    <\equation*>
      <with|font-base-size|10|<long-arrow|\<rubber-rightarrow\>|c<rsub|m>\<mapsto\>c<rsub|m>-c<rsub|k>*q<rsub|m>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|7|7|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k+1,k>>|<cell|B<rsub|k+1,k+1>-B<rsub|k+1,k>*q<rsub|k+1>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m>-B<rsub|k+1,k>*q<rsub|m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k>>|<cell|B<rsub|n,k+1>-B<rsub|n,k>*q<rsub|k+1>>|<cell|\<cdots\>>|<cell|B<rsub|n,m>-B<rsub|n,k>*q<rsub|m>>>>>>|)>=:B<rprime|'>>
    </equation*>

    For <math|k\<less\>i\<leqslant\>n> let <math|p<rsub|i>> be such that
    <math|B<rsub|i,k>=p<rsub|i>B<rsub|k,k>>. Apply elementary row operations

    <\equation*>
      B<rprime|'><long-arrow|\<rubber-rightarrow\>|r<rsub|k+1>\<mapsto\>r<rsub|k+1>-p<rsub|k+1>*r<rsub|k>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|7|7|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|B<rsub|k+1,k+1><rprime|''>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m><rprime|''>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k+1,k><rprime|'>>|<cell|B<rsub|k+2,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|k+2,m>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|n,k><rprime|'>>|<cell|B<rsub|n,k+1><rprime|'>>|<cell|\<cdots\>>|<cell|B<rsub|n,m><rprime|'>>>>>>|)>
    </equation*>

    <\equation*>
      <long-arrow|\<rubber-rightarrow\>|r<rsub|n>\<mapsto\>r<rsub|n>-p<rsub|n>*r<rsub|k>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|6|6|cell-halign|c>|<cwith|1|-1|7|7|cell-halign|c>|<cwith|1|-1|7|7|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1,1>>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|B<rsub|k,k>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|B<rsub|k+1,k+1><rprime|''>>|<cell|\<cdots\>>|<cell|B<rsub|k+1,m><rprime|''>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|0>|<cell|B<rsub|n,k+1><rprime|''>>|<cell|\<cdots\>>|<cell|B<rsub|n,m><rprime|''>>>>>>|)>=:B<rsup|\<prime\>*\<prime\>>
    </equation*>

    Then <math|B<rprime|''>\<sim\><rsub|\<cal-E\>>B<rprime|'>\<sim\><rsub|\<cal-E\>>B\<sim\><rsub|\<cal-E\>>A>
    and <math|B<rprime|''>\<in\>\<cal-A\><rsub|k+1>>. The inductive step is
    complete. It follows that <math|\<cal-A\><rsub|min{m,n}+1>\<neq\>\<emptyset\>>;
    any <math|B> in this set is diagonal and equivalent to <math|A>.
  </proof>

  For <math|d<rsub|1>,\<ldots\>,d<rsub|n>\<in\>\<bbb-N\><rsub|0>> and
  <math|B<rsub|1>\<in\>M<rsub|d<rsub|1>>(R),\<ldots\>,B<rsub|n>\<in\>M<rsub|d<rsub|n>>(R)>
  we write

  <\equation*>
    B<rsub|1>\<oplus\>\<cdots\>\<oplus\>B<rsub|n>\<assign\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|B<rsub|1>>|<cell|0<rsub|d<rsub|1>\<times\>d<rsub|2>>>|<cell|\<cdots\>>|<cell|0<rsub|d<rsub|1>\<times\>d<rsub|n>>>>|<row|<cell|0<rsub|d<rsub|2>\<times\>d<rsub|1>>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0<rsub|d<rsub|n-1>\<times\>d<rsub|n>>>>|<row|<cell|0<rsub|d<rsub|n>\<times\>d<rsub|1>>>|<cell|\<cdots\>>|<cell|0<rsub|d<rsub|n>\<times\>d<rsub|n-1>>>|<cell|B<rsub|n>>>>>>|)>
  </equation*>

  \;

  We call the <math|B<rsub|i>>s the <strong|blocks> of the matrix
  <math|B<rsub|1>\<varoplus\>\<cdots\>\<varoplus\>B<rsub|n>>, and it will be
  useful to allow `degenerate' 0\<times\>0 blocks.

  <\example>
    A matrix <math|A\<in\>M<rsub|n>(R)> is diagonal with entries
    <math|d<rsub|1<rsub|>>,\<ldots\>,d<rsub|n>> if
    <math|A=(d<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>(d<rsub|n>)>.
  </example>

  <\example>
    If <math|d<rsub|1>+\<cdots\>+d<rsub|n>=n> then
    <math|I<rsub|n>=I<rsub|d<rsub|1>>\<varoplus\>\<cdots\>\<varoplus\>I<rsub|d<rsub|n>>>.
    <with|font|Segoe UI Emoji|\<#26A0\>>This is <em|not> a special case of
    the previous example because we are allowing <math|0\<times\>0> blocks.
  </example>

  <\observation>
    If <math|B<rsub|i>\<sim\>B<rprime|'><rsub|i>> (resp.
    <math|B<rsub|i>\<sim\><rsub|\<cal-E\>>B<rprime|'><rsub|i>>) for
    <math|1\<leqslant\>i\<leqslant\>n> then
    <math|B<rsub|1>\<varoplus\>\<cdots\>\<varoplus\>B<rsub|n>\<sim\>B<rprime|'><rsub|1>\<varoplus\>\<cdots\>\<varoplus\>B<rsub|n><rprime|'>>
    (resp. <math|B<rsub|1>\<varoplus\>\<cdots\>\<varoplus\>B<rsub|n><math|\<sim\><rsub|\<cal-E\>>>B<rprime|'><rsub|1>\<varoplus\>\<cdots\>\<varoplus\>B<rsub|n><rprime|'>>).
  </observation>

  <\lemma>
    Suppose that <math|R> is an integral domain, <math|k\<less\>l> and
    <math|A\<in\>M<rsub|n,m>(R)> is diagonal with
    <math|\<langle\>d\<rangle\>=\<langle\>A<rsub|k,k>\<rangle\>+\<langle\>A<rsub|l,l>\<rangle\>>
    for some <math|d\<neq\>0>, and <math|m*d=A<rsub|l,l>A<rsub|k,k>>. Then
    <math|A> is equivalent by elementary operations to the matrix <math|A>
    with <math|A<rsub|k,k>> replaced by <math|m> and <math|A<rsub|l,l>>
    replaced by <math|d>.
  </lemma>

  <\proof>
    Let <math|\<alpha\>,\<beta\>,p,q\<in\>R> be such that
    <math|A<rsub|k,k>\<alpha\>+\<beta\>A<rsub|l,l>=d> and
    <math|A<rsub|k,k>=d*p,A<rsub|l,l>=q*d>, and so <math|m=q*d*p>. Then

    <\equation*>
      A<long-arrow|\<rubber-rightarrow\>|c<rsub|l>\<mapsto\>c<rsub|l>+c<rsub|k>\<alpha\>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|l>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|l>|<cwith|1|-1|3|3|cell-halign|l>|<cwith|1|-1|4|4|cell-halign|l>|<cwith|1|-1|5|5|cell-halign|l>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<ddots\>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|A<rsub|k,k>>|<cell|>|<cell|A<rsub|k,k>*\<alpha\>>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<ddots\>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|A<rsub|l,l>>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|\<ddots\>>>>>>|)><long-arrow|\<rubber-rightarrow\>|r<rsub|k>\<mapsto\>r<rsub|k>+\<beta\>r<rsub|l>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<ddots\>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|A<rsub|k,k>>|<cell|>|<cell|d>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<ddots\>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|A<rsub|l,l>>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|\<ddots\>>>>>>|)><long-arrow|\<rubber-rightarrow\>|c<rsub|k>\<mapsto\>c<rsub|k>-c<rsub|l>*p>
    </equation*>

    <\equation*>
      <around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<ddots\>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|0>|<cell|>|<cell|d>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<ddots\>>|<cell|>|<cell|>>|<row|<cell|>|<cell|-m>|<cell|>|<cell|A<rsub|l,l>>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|\<ddots\>>>>>>|)><long-arrow|\<rubber-rightarrow\>|r<rsub|l>\<mapsto\>r<rsub|l>-q*r<rsub|k>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<ddots\>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|0>|<cell|>|<cell|d>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<ddots\>>|<cell|>|<cell|>>|<row|<cell|>|<cell|-m>|<cell|>|<cell|0>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|\<ddots\>>>>>>|)><long-arrow|\<rubber-rightarrow\>|r<rsub|l>\<leftrightarrow\>r<rsub|k>>
    </equation*>

    <\equation*>
      <around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|l>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|l>|<cwith|1|-1|3|3|cell-halign|l>|<cwith|1|-1|4|4|cell-halign|l>|<cwith|1|-1|5|5|cell-halign|l>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<ddots\>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|-m>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<ddots\>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|d>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|\<ddots\>>>>>>|)><long-arrow|\<rubber-rightarrow\>|r<rsub|k>\<leftrightarrow\><around*|(|-1|)>r<rsub|k>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|l>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|l>|<cwith|1|-1|3|3|cell-halign|l>|<cwith|1|-1|4|4|cell-halign|l>|<cwith|1|-1|5|5|cell-halign|l>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<ddots\>>|<cell|>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|m>|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|\<ddots\>>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|d>|<cell|>>|<row|<cell|>|<cell|>|<cell|>|<cell|>|<cell|\<ddots\>>>>>>|)>
    </equation*>

    The result is proved.
  </proof>

  We say that <math|A\<in\>M<rsub|n,m>(R)> is in <strong|Smith normal form>
  over <math|R> if it is diagonal and <math|A<rsub|i,i>\<divides\>A<rsub|i+1,i+1>>
  for all <math|1\<leqslant\>i\<less\>min{n,m}>.

  <\example*>
    <matrix|<tformat|<table|<row|<cell|2>|<cell|0>>|<row|<cell|0>|<cell|3>>>>>
    is in Smith normal form in <math|\<bbb-Q\>> but not in <math|\<bbb-Z\>>.
    The preceding lemma shows

    <\equation*>
      <matrix|<tformat|<table|<row|<cell|2>|<cell|0>>|<row|<cell|0>|<cell|3>>>>>\<rightarrow\><matrix|<tformat|<table|<row|<cell|2>|<cell|-2>>|<row|<cell|0>|<cell|3>>>>>\<rightarrow\><matrix|<tformat|<table|<row|<cell|2>|<cell|1>>|<row|<cell|0>|<cell|3>>>>>\<rightarrow\><matrix|<tformat|<table|<row|<cell|0>|<cell|1>>|<row|<cell|-6>|<cell|3>>>>>\<rightarrow\><matrix|<tformat|<table|<row|<cell|0>|<cell|1>>|<row|<cell|-6>|<cell|0>>>>>\<rightarrow\><matrix|<tformat|<table|<row|<cell|1>|<cell|0>>|<row|<cell|0>|<cell|-6>>>>>\<rightarrow\><matrix|<tformat|<table|<row|<cell|1>|<cell|0>>|<row|<cell|0>|<cell|6>>>>>
    </equation*>
  </example*>

  <\proposition>
    Suppose that <math|R> is a Bezout domain. Then every diagonal matrix
    <math|A\<in\>M<rsub|n,m>(R)> is equivalent by elementary operations to a
    matrix in Smith normal form.
  </proposition>

  <\proof>
    Let <math|\<cal-A\><rsub|k>> be the set of diagonal matrices that are
    elementarily equivalent to <math|A>, and such that if the diagonal
    entries are denoted <math|a<rsub|1>,a<rsub|2>,\<ldots\>,a<rsub|min{m,n}>>,
    then <math|a<rsub|i>\<mid\>a<rsub|j>> whenever
    <math|1\<leqslant\>i\<leqslant\>j> and <math|i\<leqslant\>k>. Certainly
    <math|A\<in\>\<cal-A\><rsub|0>> since the hypotheses on the entries is
    vacuous then, so there is a maximal <math|k\<in\>\<bbb-N\><rsup|\<ast\>>>
    with <math|k\<minus\>1\<leqslant\>min{m,n}> such that
    <math|\<cal-A\><rsub|k\<minus\>1>> is non-empty.

    By maximality of <math|k> for each matrix in
    <math|\<cal-A\><rsub|k\<minus\>1>> with diagonal entries <math|a<rsub|1>,
    a<rsub|2>,\<ldots\>,a<rsub|min{m,n}>> there is a minimal <math|l\<gtr\>k>
    with <math|a<rsub|k>\<nmid\>a<rsub|l>>; let
    <math|B\<in\>\<cal-A\><rsub|k\<minus\>1>> have <math|l> maximal with this
    property. By Lemma 6.10 and Proposition 3.22 we can replace
    <math|a<rsub|k>> and <math|a<rsub|l>> by the greatest common divisor and
    least common multiple respectively of <math|a<rsub|k>> and
    <math|a<rsub|l>>, to get a matrix <math|C> that is equivalent to <math|B>
    by elementary operations.

    Write <math|a<rprime|'><rsub|1>,\<ldots\>,a<rprime|'><rsub|min{m,n}>> for
    the diagonal entries of <math|C>, so that for <math|i\<nin\>{k,l}> we
    have <math|a<rprime|'><rsub|i>= a<rsub|i>>. <math|a<rprime|'><rsub|k>>
    and <math|a<rprime|'><rsub|l>> are linear combinations of
    <math|a<rsub|k>> and <math|a<rsub|l>> and so for
    <math|i\<leqslant\>k\<minus\>1>, <math|a<rprime|'><rsub|i>> divides them
    both, and hence for <math|1\<leqslant\>i\<leqslant\>j> we have
    <math|a<rprime|'><rsub|i>\<divides\>a<rprime|'><rsub|j>>. It follows that
    <math|C\<in\>\<cal-A\><rsub|k\<minus\>1>>. Finally
    <math|a<rprime|'><rsub|k>\<divides\>a<rsub|k>> and so
    <math|a<rprime|'><rsub|k>\<mid\> a<rprime|'><rsub|j>> for
    <math|k\<leqslant\>j\<less\>l>, but also
    <math|a<rprime|'><rsub|k>\<mid\>a<rprime|'><rsub|l>> contradicting
    maximality of <math|l>. The result is proved.
  </proof>

  <\theorem>
    Suppose that <math|R> is a Euclidean domain. Then every
    <math|A\<in\>M<rsub|n,m>(R)> is equivalent by elementary operations to a
    matrix in Smith normal form.
  </theorem>

  <\proof>
    This follows from Theorem 6.6 and Proposition 6.11.
  </proof>

  <\remark>
    Following the work of Kaplanksy [Kap49] an integral domain <math|R> for
    which every <math|A\<in\>M<rsub|n,m>(R)> is equivalent to a matrix in
    Smith normal form, is called an <strong|elementary divisor domain>, so in
    this language Theorem 6.12 shows that every Euclidean domain is an
    elementary divisor domain.
  </remark>

  In the other direction Kaplansky showed [LLS74, Theorem 3.1] that every
  elementary divisor domain is a Bezout domain, and it is an open problem
  [Lor12] (going back at least to [Hel43]) to give an example of a Bezout
  domain that that is not an elementary divisor domain.

  <section|Applications of Smith normal form>

  With these tools we are in a position to describe the structure of finitely
  generated modules over a Euclidean domain:

  <\theorem>
    Suppose that <math|R> is a Euclidean domain and <math|M> is generated by
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>>[Since ED is PID, every module is
    finitely generated]. Then there are elements
    <math|a<rsub|1>\<divides\>a<rsub|2>\<divides\>\<cdots\>\<divides\>a<rsub|n>>
    in <math|R> and a matrix <math|Q\<in\>GL<rsub|n>(R)> such that

    <\eqnarray*>
      <tformat|<table|<row|<cell|(R/\<langle\>a<rsub|1>\<rangle\>)\<varoplus\>\<cdots\>\<varoplus\>(R/\<langle\>a<rsub|n>\<rangle\>)>|<cell|\<rightarrow\>>|<cell|M>>|<row|<cell|(r<rsub|1>+\<langle\>a<rsub|1>\<rangle\>,\<ldots\>,r<rsub|n>+\<langle\>a<rsub|n>\<rangle\>)>|<cell|\<mapsto\>>|<cell|<math|>(r*Q)<rsub|1>.x<rsub|1>+\<cdots\>+(r*Q)<rsub|n>.x<rsub|n>>>>>
    </eqnarray*>

    is a well-defined <math|R>-linear isomorphism.
  </theorem>

  <\proof>
    The map

    <\equation*>
      \<Phi\><rsub|x>:R<rsup|n>\<rightarrow\>M;r\<mapsto\>r<rsub|1>.x<rsub|1>+\<cdots\>+r<rsub|n>.x<rsub|n>
    </equation*>

    <math|>is an <math|R>-linear surjection. Since <math|R> is a Euclidean
    domain it is a PID and hence by Proposition 5.29 there is
    <math|A\<in\>M<rsub|n>(R)> such that the kernel of this map is
    <math|R<rsup|n>A>. By Theorem 6.12 there is a diagonal matrix
    <math|B\<in\>M<rsub|n>(R)> with entries
    <math|a<rsub|1>\<divides\>\<ldots\>\<divides\>a<rsub|n>> and
    <math|P,Q\<in\>GL<rsub|n>(R)> such that <math|A=P*B*Q>. The map

    <\equation*>
      R<rsup|n>\<rightarrow\>M;r\<mapsto\>(r*Q)<rsub|1>.x<rsub|1>+\<cdots\>+(r*Q)<rsub|n>.x<rsub|n>
    </equation*>

    is an <math|R>-linear map which is surjective because <math|Q> is
    invertible and <math|\<Phi\><rsub|x>> is surjective. The kernel is the
    set of <math|r\<in\>R<rsup|n>> for which <math|r*Q\<in\>ker
    \<Phi\><rsub|x>> <em|i.e.> for which there is
    <math|r<rprime|'>\<in\>R<rsup|n>> such that <math|r*Q=r<rprime|'>A>. This
    is true if and only if <math|r=(r<rprime|'>P)(P<rsup|\<minus\>1>A*Q<rsup|-1>)=(r<rprime|'>P)B>.
    Since <math|P> is invertible <math|r> is in the kernel if and only if
    <math|r\<in\>R<rsup|n>B=\<langle\>a<rsub|1>\<rangle\>\<varoplus\>\<cdots\>\<varoplus\>\<langle\>a<rsub|n>\<rangle\>>.
    Finally, the composition of maps

    <\equation*>
      <tabular*|<tformat|<table|<row|<cell|(R/\<langle\>a<rsub|1>\<rangle\>)\<varoplus\>\<cdots\>\<varoplus\>(R/\<langle\>a<rsub|n>\<rangle\>)>|<cell|\<rightarrow\>>|<cell|<math|>R<rsup|n>/R<rsup|n>B>|<cell|\<rightarrow\>>|<cell|M>>|<row|<cell|(r<rsub|1>+\<langle\>a<rsub|1>\<rangle\>,\<ldots\>,r<rsub|n>+\<langle\>a<rsub|n>\<rangle\>)>|<cell|\<mapsto\>>|<cell|r+\<langle\>a<rsub|1>\<rangle\>\<varoplus\>\<cdots\>\<varoplus\>\<langle\>a<rsub|n>\<rangle\>>|<cell|\<mapsto\>>|<cell|(r*Q)<rsub|1>.x<rsub|1>+\<cdots\>+(r*Q)<rsub|n>.x<rsub|n>>>>>>
    </equation*>

    <math|<math|><math|>>is a composition of well-defined <math|R>-linear
    isomorphisms by the First Isomorphism Theorem.
  </proof>

  This in turn lets us describe the structure of finitely generated
  commutative groups:

  <\corollary>
    Suppose that <math|G> is a commutative group generated by
    <math|x<rsub|1>,\<ldots\>,x<rsub|n>>. Then there are natural numbers
    <math|d<rsub|1>\<divides\>d<rsub|2>\<divides\>\<cdots\>\<divides\>d<rsub|n>>
    (if <math|d<rsub|i>=0> then <math|d<rsub|i+1>=\<cdots\>=d<rsub|n>=0>)
    such that <math|G> is isomorphic to <math|\<bbb-Z\>/\<langle\>d<rsub|1>\<rangle\>\<varoplus\>\<cdots\>\<varoplus\>\<bbb-Z\>/\<langle\>d<rsub|n>\<rangle\>>.
    Write <math|d<rsub|i>> as product of prime powers, then use Chinese
    remainder theorem <math|\<bbb-Z\><rsup|s>\<oplus\>\<bbb-Z\>/\<langle\>p<rsub|1><rsup|a<rsub|1>>\<rangle\>\<varoplus\>\<cdots\>\<varoplus\>\<bbb-Z\>/\<langle\>p<rsub|m><rsup|a<rsub|m>>\<rangle\>>
  </corollary>

  <\proof>
    This is a corollary of Theorem 7.1 since a commutative group is a
    <math|\<bbb-Z\>>-module, and <math|\<bbb-Z\>> is a Euclidean domain. We
    may ensure the <math|d<rsub|i>>s are natural numbers by multiplying by a
    unit in <math|\<bbb-Z\>> as necessary.
  </proof>

  <subsection|Matrix forms>

  In this section we work with matrices multiplying columns on the left
  rather than rows on the right [this is not linear, if underlying ring is
  not commutative]. Equivalent matrices induce isomorphisms in the same way
  as in the proof of Theorem 7.1:

  <\proposition>
    Suppose that <math|A,B\<in\>M<rsub|n>(\<bbb-F\>[X])>, and
    <math|P,Q\<in\>GL<rsub|n>(\<bbb-F\>[X])> are such that <math|A=P*B*Q>.
    Then the map

    <\equation*>
      \<bbb-F\>[X]<rsup|n><rsub|<text|col>>/A\<bbb-F\><around*|[|X|]><rsup|n><rsub|<text|col>>\<rightarrow\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/B\<bbb-F\>[*X]<rsup|m><rsub|<text|col>>;x+A\<bbb-F\>[X<math|]<rsup|n><rsub|<text|col>>>\<mapsto\>P<rsup|\<minus\>1>x+B\<bbb-F\>[X]<rsup|n><rsub|<text|col>>
    </equation*>

    \ is a well-defined <math|\<bbb-F\>[X]>-linear isomorphism.
  </proposition>

  <\proof>
    Since <math|\<bbb-F\>[X]> is commutative
    <math|B\<bbb-F\>[X]<rsup|n><rsub|<text|col>>> is an
    <math|\<bbb-F\>[X]>-module, and hence
    <math|\<bbb-F\>[X]<rsup|n><rsub|<text|col>>\<rightarrow\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/B\<bbb-F\>[X]<rsup|n><rsub|<text|col>>;x\<mapsto\>P<rsup|\<minus\>1>x+B\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>
    is a well-defined <math|\<bbb-F\>[X]>-linear surjection. It has kernel
    <math|A\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>, since
    <math|P<rsup|\<minus\>1>x\<in\>B\<bbb-F\>[X]<rsup|n><rsub|<text|col>>> if
    and only if <math|P<rsup|\<minus\>1>x=B*x<rprime|'>> for some
    <math|x<rprime|'>\<in\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>, but
    <math|P<rsup|\<minus\>1>x=B*x<rprime|'>> if and only if
    <math|x=(P*B*Q)(Q<rsup|\<minus\>1>x<rprime|'>)=A(Q<rsup|\<minus\>1>x<rprime|'>)>,
    and hence <math|P<rsup|\<minus\>1>x\<in\>B\<bbb-F\>[X]<rsup|n><rsub|col>>
    if and only if <math|x=A*x<rprime|''>> for some
    <math|x<rprime|''>\<in\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>> since
    <math|Q> is invertible. The result then follows by the First Isomorphism
    Theorem.
  </proof>

  For <math|p=a<rsub|0>+\<cdots\>+a<rsub|d>X<rsup|d>\<in\>\<bbb-F\>[X]> and
  <math|C\<in\>M<rsub|n>(\<bbb-F\>[X])> write <math|p.C> for the matrix with
  <math|(p.C)<rsub|i,j>=p(X)C<rsub|i,j>(X)> \U the . is the scalar
  multiplication in the <math|\<bbb-F\>[X]>-module
  <math|M<rsub|n>(\<bbb-F\>[X])> \U and write <math|p(C)> the evaluation
  homomorphism at <math|C> extending the ring homomorphism
  <math|\<bbb-F\>\<rightarrow\>M<rsub|n>(\<bbb-F\>[X])>, which is a
  composition of the inclusion homomorphism
  <math|\<bbb-F\>\<rightarrow\>\<bbb-F\>[X]> and the diagonal homomorphism
  <math|\<bbb-F\>[X]\<rightarrow\>M<rsub|n>(\<bbb-F\>[X])> <em|i.e.>

  <\equation*>
    p(C)=a<rsub|0>.I<rsub|n>+\<cdots\>+a<rsub|d>.C<rsup|d>
  </equation*>

  <\lemma>
    Suppose that <math|A\<in\>M<rsub|n>(\<bbb-F\>)>. Then
    <math|e<rsup|t><rsub|1>+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|col>,\<ldots\>,e<rsup|t><rsub|n>+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>
    is a basis of the <math|\<bbb-F\>>-vector space
    <math|\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>.
  </lemma>

  <\proof>
    Since the matrix <math|X.I<rsub|n>> is in the centre of
    <math|M<rsub|n>(\<bbb-F\>[X])>,

    <\equation*>
      (X.I<rsub|n>)<rsup|i>\<minus\>A<rsup|i>=(X.I<rsub|n>\<minus\>A)((X.I<rsub|n>)<rsup|i\<minus\>1>+\<cdots\>+A<rsup|i\<minus\>1>);
    </equation*>

    and since <math|\<bbb-F\>[X]> is commutative, left multiplication in
    <math|M<rsub|n>(\<bbb-F\>[X])> is <math|\<bbb-F\>[X]>-linear, so

    <\equation*>
      p(X.I<rsub|n>)\<minus\>p(A)=(X.I<rsub|n>\<minus\>A)<big|sum><rsub|i=1><rsup|d>a<rsub|i>.(A<rsup|i\<minus\>1>+\<cdots\>+(X.I<rsub|n>)<rsup|i\<minus\>1>)=(X.I<rsub|n>\<minus\>A)Q
    </equation*>

    for some <math|Q\<in\>M<rsub|n>(\<bbb-F\>[X])>. Now, the map

    <\equation*>
      \<Phi\>:\<bbb-F\>[X]<rsup|n><rsub|<text|col>>\<rightarrow\>\<bbb-F\><rsup|n><rsub|<text|col>>;p\<mapsto\>p<rsub|1>(A)e<rsup|t><rsub|1>+\<cdots\>+p<rsub|n>(A)e<rsup|t><rsub|n>
    </equation*>

    is <math|\<bbb-F\>>-linear, and to identify its kernel we use the same
    method of proof as for the Factor Theorem: Specifically, for
    <math|p\<in\>ker \<Phi\>> we have

    <\eqnarray*>
      <tformat|<table|<row|<cell|p=p\<minus\>\<Phi\>(p)>|<cell|=>|<cell|(p<rsub|1>(X.I<rsub|n>)\<minus\>p<rsub|1>(A))e<rsup|t><rsub|1>+\<cdots\>+(p<rsub|n>(X.I<rsub|n>)\<minus\>p<rsub|n>(A))e<rsup|t><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|(X.I<rsub|n>
      \<minus\>A)(Q<rsub|1>e<rsup|t><rsub|1>+\<cdots\>+Q<rsub|n>e<rsup|t><rsub|n>),>>>>
    </eqnarray*>

    for <math|Q<rsub|1>,\<ldots\>,Q<rsub|n>\<in\>M<rsub|n>(\<bbb-F\>[X])>. In
    particular, <math|p\<in\>(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>.

    In the other direction, <math|e<rsup|t><rsub|1>+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>,\<ldots\>,e<rsup|t><rsub|n>+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>
    is <math|\<bbb-F\>>-linearly independent as a subsequence of the subspace
    <math|\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>.
    To see this, suppose <math|p=(X.I<rsub|n>\<minus\>A)q,p\<in\>\<bbb-F\><rsup|n><rsub|<text|col>>,q\<in\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>
    is not identically 0 then there is <math|i> such that <math|deg
    q<rsub|i>> maximal, then <math|0=deg p<rsub|i>=1+deg q<rsub|i>>,
    contradiction.

    Finally, the vectors <math|e<rsup|t><rsub|1>+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>,\<ldots\>,e<rsup|t><rsub|n>+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>
    are also spanning since <math|\<Phi\>(e<rsup|t><rsub|i>)=e<rsup|t><rsub|i>>
    for all <math|1\<leqslant\>i\<leqslant\>n>, and
    <math|e<rsup|t><rsub|1>,\<ldots\>,e<rsup|t><rsub|n>> is a spanning subset
    of <math|\<bbb-F\><rsup|n><rsub|<text|col>>>. The result is proved.
  </proof>

  <\proposition>
    Suppose that <math|A,B\<in\>M<rsub|n>(\<bbb-F\>)>. Then
    <math|X.I<rsub|n>\<minus\>A> and <math|X.I<rsub|n>\<minus\>B> are
    equivalent as matrices in <math|M<rsub|n>(\<bbb-F\>[X])> if and only if
    <math|A> and <math|B> are similar as matrices in
    <math|M<rsub|n>(\<bbb-F\>)>.
  </proposition>

  <\proof>
    If <math|A> and <math|B> are similar then there is
    <math|P\<in\>GL<rsub|n>(F)> such that <math|A=P*B*P<rsup|\<minus\>1>>,
    but then <math|X.I<rsub|n>\<minus\>A=P(X.I<rsub|n>\<minus\>B)P<rsup|\<minus\>1>>
    and <math|X.I<rsub|n>\<minus\>A> is similar, and so equivalent, to
    <math|X.I<rsub|n>\<minus\>B> as matrices in
    <math|M<rsub|n>(\<bbb-F\>[X])>.

    In the other direction, since <math|X.I<rsub|n>\<minus\>A\<sim\>X.I<rsub|n>\<minus\>B>,
    Proposition 7.3 gives an <math|\<bbb-F\>[X]>-linear isomorphism

    <\equation*>
      \<Phi\>:\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>\<rightarrow\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/(X.I<rsub|n>\<minus\>B)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>.
    </equation*>

    By Lemma 7.4 we know <math|e<rsup|t><rsub|1>+(X.I<rsub|n>
    \<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>,\<ldots\>,e<rsup|t><rsub|n>
    +(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>> is an
    <math|\<bbb-F\>>-basis for <math|\<bbb-F\>[X]<rsup|n><rsub|<text|col>>/(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>,
    and similarly with <math|A> replaced by <math|B>. Since <math|\<Phi\>>
    is, in particular, an <math|\<bbb-F\>>-linear bijection we conclude that
    there is <math|P\<in\>GL<rsub|n>(\<bbb-F\>)> such that

    <\equation*>
      \<Phi\>(v+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>)=P
      v+(X.I<rsub|n>\<minus\>B)\<bbb-F\>[X]<rsup|n><rsub|<text|col>><text|
      for all >v\<in\>\<bbb-F\><rsup|n><rsub|<text|col>>.
    </equation*>

    Now, <math|\<Phi\>> is <math|\<bbb-F\>[X]>-linear, so for
    <math|v\<in\>\<bbb-F\><rsup|n><rsub|<text|col>>> we have

    <\align*>
      <tformat|<table|<row|<cell|0>|<cell|=\<Phi\>((X.I<rsub|n>\<minus\>A)v+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>)>>|<row|<cell|>|<cell|=X\<Phi\>(v+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>)\<minus\>\<Phi\>(A*v+(X.I<rsub|n>\<minus\>A)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>)>>|<row|<cell|>|<cell|=X*P*v\<minus\>P*A*v+(X.I<rsub|n>\<minus\>B)\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>>>>
    </align*>

    In other words, <math|X*P*v\<minus\>P*A*v=X*w\<minus\>B*w> for some
    <math|w\<in\>\<bbb-F\>[X]<rsup|n><rsub|<text|col>>>. Since
    <math|v\<in\>\<bbb-F\><rsub|<text|col>><rsup|n>>, no entry on the left
    can have a non-zero coefficient of <math|X<rsup|i>> for any
    <math|i\<geqslant\>2>, and hence <math|w\<in\>\<bbb-F\><rsup|n><rsub|<text|col>>>.
    Equating coefficients we have <math|w=P*v> and <math|P*A*v=B*w>, and
    hence <math|A*v=P<rsup|\<minus\>1>B*P*v>. Since <math|v> was arbitrary we
    have that <math|A=P<rsup|\<minus\>1>B*P> as claimed.
  </proof>

  Given a monic polynomial <math|f(X)=X<rsup|d>+a<rsub|d\<minus\>1>X<rsup|d\<minus\>1>+\<cdots\>+a<rsub|0>\<in\>\<bbb-F\>[X]<rsup|\<ast\>>>
  we define the <math|d\<times\>d> matrices

  <\equation*>
    C(f)\<assign\><matrix|<tformat|<table|<row|<cell|0>|<cell|\<cdots\>>|<cell|\<cdots\>>|<cell|0>|<cell|-a<rsub|0>>>|<row|<cell|1>|<cell|\<ddots\>>|<cell|>|<cell|\<vdots\>>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<ddots\>>|<cell|0>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|1>|<cell|-a<rsub|d-1>>>>>><text|
    and >D<around|(|f|)>\<assign\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|f<around|(|X|)>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|1>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|1>>>>>|)>
  </equation*>

  The matrix <math|C(f)> is called the <strong|companion matrix> to <math|f>.
  <with|font|Segoe UI Emoji|\<#26A0\>>We allow <math|d=0> when these are
  `empty' <math|0\<times\>0> matrices.

  <\example>
    For <math|f(X)\<in\>\<bbb-F\>[X]<rsup|\<ast\>>> we have
    <math|X.I<rsub|d>\<minus\>C(f)\<sim\><rsub|\<cal-E\>>D(f)>. To see this
    write <math|f(X)=X<rsub|d>+a<rsub|d\<minus\>1>X<rsup|d\<minus\>1>+\<cdots\>+a<rsub|0>>,
    and put <math|f<rsub|0>(X)=1> and <math|f<rsub|i>=X*f<rsub|i\<minus\>1>(X)+a<rsub|d\<minus\>i>>
    for <math|1\<leqslant\>i\<leqslant\>d> so that
    <math|f<rsub|1>(X)=X+a<rsub|d\<minus\>1>> and <math|f<rsub|d>(X)=f(X)>;
    and apply row and column operations in four groups:
  </example>

  <\align*>
    <tformat|<table|<row|<cell|X.*I<rsub|d>-C<around|(|f|)>=>|<cell|<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|X>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|a<rsub|0>>>|<row|<cell|-1>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|X>|<cell|a<rsub|d-2>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|-1>|<cell|X+a<rsub|d-1>>>>>>|)>>>|<row|<cell|<long-arrow|\<rubber-rightarrow\>|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|r<rsub|d\<minus\>1>\<mapsto\>r<rsub|d\<minus\>1>+X*r<rsub|d>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|1>\<mapsto\>r<rsub|1>+X*r<rsub|2>>>>>>>>|<cell|<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|0>|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|f<rsub|d><around|(|X|)>>>|<row|<cell|-1>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>|<cell|\<vdots\>>>|<row|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>|<cell|f<rsub|2><around|(|X|)>>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|-1>|<cell|f<rsub|1><around|(|X|)>>>>>>|)>>>|<row|<cell|<long-arrow|\<rubber-rightarrow\>|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|c<rsub|1>\<leftrightarrow\>c<rsub|d>>>|<row|<cell|\<vdots\>>>|<row|<cell|c<rsub|d-1>\<leftrightarrow\>c<rsub|d>>>>>>>>|<cell|<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|f<rsub|d><around|(|X|)>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|-1>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|-1>>>>>|)>>>|<row|<cell|<long-arrow|\<rubber-rightarrow\>|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|c<rsub|2>\<mapsto\><around*|(|-1|)>c<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|c<rsub|d>\<mapsto\><around*|(|-1|)>c<rsub|d>>>>>>>>|<cell|D(f<rsub|d>)=D(f).>>>>
  </align*>

  <with|font|Segoe UI Emoji|\<#26A0\>>The order of the row operations in the
  first group and the column operations in the third group matter, so we do
  <math|r<rsub|d\<minus\>1>\<mapsto\>r<rsub|d\<minus\>1>+X*r<rsub|d>> first
  and <math|r<rsub|1>\<mapsto\>r<rsub|1>+X*r<rsub|2>> last in the first
  group, and <math|c<rsub|d>\<mapsto\>c<rsub|d>+f<rsub|1>(X)c<rsub|d\<minus\>1>>
  first and <math|c<rsub|d>\<mapsto\>c<rsub|d>+f<rsub|d\<minus\>1>(X)c<rsub|1>>
  last in the third group; in the other two groups the operations commute.

  For <math|\<lambda\>\<in\>\<bbb-F\>> and <math|d\<in\>\<bbb-N\><rsub|0>>
  define the <strong|<math|d>-dimensional Jordan matrix with eigenvalue
  <math|\<lambda\>>> to be the (possibly empty) <math|d\<times\>d>-matrix

  <\equation*>
    J(\<lambda\>,d)\<assign\><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|\<lambda\>>|<cell|1>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|\<lambda\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<ddots\>>|<cell|\<lambda\>>|<cell|1>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|\<cdots\>>|<cell|0>|<cell|\<lambda\>>>>>>|)><text|;
    and recall >D((X\<minus\>\<lambda\>)<rsup|d>)=<around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|<around|(|X-\<lambda\>|)><rsup|d>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|1>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|1>>>>>|)>
  </equation*>

  <\example>
    For <math|\<lambda\>\<in\>\<bbb-F\>> we have
    <math|X.I<rsub|d>\<minus\>J(\<lambda\>,d)\<sim\><rsub|\<cal-E\>>D((X\<minus\>\<lambda\>)<rsup|d>)>.

    To see this note that <math|X.I<rsub|d>\<minus\>J(\<lambda\>,d)> equals

    <\equation*>
      <around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|X-\<lambda\>>|<cell|-1>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|X-\<lambda\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<ddots\>>|<cell|X-\<lambda\>>|<cell|-1>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|\<cdots\>>|<cell|0>|<cell|X-\<lambda\>>>>>>|)><long-arrow|\<rubber-rightarrow\>|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|c<rsub|d\<minus\>1>\<mapsto\>c<rsub|d\<minus\>1>+<around*|(|X-\<lambda\>|)>*c<rsub|d>>>|<row|<cell|\<vdots\>>>|<row|<cell|c<rsub|1>\<mapsto\>c<rsub|1>+<around*|(|X-\<lambda\>|)>c<rsub|2>>>>>>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|c>|<cwith|1|-1|5|5|cell-rborder|0ln>|<table|<row|<cell|0>|<cell|-1>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|0>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<ddots\>>|<cell|0>|<cell|-1>>|<row|<cell|<around|(|X-\<lambda\>|)><rsup|d>>|<cell|\<cdots\>>|<cell|\<cdots\>>|<cell|0>|<cell|0>>>>>|)>
    </equation*>

    <\equation*>
      <long-arrow|\<rubber-rightarrow\>|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|r<rsub|1>\<leftrightarrow\>r<rsub|d>>>|<row|<cell|\<vdots\>>>|<row|<cell|r<rsub|d-1>\<leftrightarrow\>r<rsub|d>>>>>>><around*|(|<tabular*|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<cwith|1|-1|1|1|cell-lborder|0ln>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|1|-1|4|4|cell-rborder|0ln>|<table|<row|<cell|<around|(|X-\<lambda\>|)><rsup|d>>|<cell|0>|<cell|\<cdots\>>|<cell|0>>|<row|<cell|0>|<cell|-1>|<cell|\<ddots\>>|<cell|\<vdots\>>>|<row|<cell|\<vdots\>>|<cell|\<ddots\>>|<cell|\<ddots\>>|<cell|0>>|<row|<cell|0>|<cell|\<cdots\>>|<cell|0>|<cell|-1>>>>>|)><long-arrow|\<rubber-rightarrow\>|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|c<rsub|2>\<mapsto\><around*|(|-1|)>c<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|c<rsub|d>\<mapsto\><around*|(|-1|)>c<rsub|d>>>>>>>D<around*|(|<around*|(|X-\<lambda\>|)><rsup|d>|)>
    </equation*>
  </example>

  <\theorem>
    Suppose that <math|A\<in\>M<rsub|n>(\<bbb-F\>)>. Then there are monic
    polynomials <math|f<rsub|1>\<mid\>\<cdots\>\<mid\>f<rsub|n>> such that
    <math|A> is similar to <math|C(f<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>C(f<rsub|n>)>.
  </theorem>

  <\proof>
    By Theorem 6.12 there are polynomials
    <math|f<rsub|1>\<mid\>\<cdots\>\<mid\>f<rsub|n>> such that
    <math|X.I<rsub|n>\<minus\>A\<sim\><rsub|\<cal-E\>>\<#2206\>(X)> where
    <math|\<#2206\>(X)> is the diagonal matrix with entries
    <math|f<rsub|1>,\<ldots\>,f<rsub|n>>. In particular, there are
    <math|P,Q\<in\>GL<rsub|n>(\<bbb-F\>[X])> such that
    <math|P(X)(X.I<rsub|n>\<minus\>A)Q(X)=\<#2206\>(X)>. Since <math|P(X)>
    and <math|Q(X)> are invertible we have <math|det P(X) det
    P(X)<rsup|\<minus\>1>=1> and hence <math|det P(X),det Q(X)\<in\>U(R)>
    (see Exercise IV.7 for the proof that determinant is multiplicative),
    hence <math|det(X.I<rsub|n>\<minus\>A)> are associates <math|det
    \<#2206\>(X)> in <math|\<bbb-F\>[X]>. In particular, since
    <math|det(X.I<rsub|n>\<minus\>A)> is monic and of degree <math|n>, none
    of <math|f<rsub|1>,\<ldots\>,f<rsub|n>> is identically 0 and so they all
    have degrees which we denote <math|d<rsub|1>,\<ldots\>,d<rsub|n>>
    respectively and satisfy <math|n=d<rsub|1>+\<cdots\>+d<rsub|n>>.
    Moreover, by multiplying by units we may assume that
    <math|f<rsub|1>,\<ldots\>,f<rsub|n>> are monic.

    By permuting columns and rows as necessary we have
    <math|\<#2206\>(X)\<sim\><rsub|\<cal-E\>>D(f<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>D(f<rsub|n>)>.
    The calculation in Example 7.6 shows us that
    <math|D(f<rsub|i>)\<sim\><rsub|\<cal-E\>>X.I<rsub|d<rsub|i>>\<minus\>C(f<rsub|i>)>
    and hence <math|X.I<rsub|n>\<minus\>A\<sim\><rsub|\<cal-E\>>X.I<rsub|n>\<minus\>C(f<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>C(f<rsub|n>)>.
    The result now follows from Proposition 7.5.
  </proof>

  A matrix is said to be in <strong|rational canonical form> if it is a block
  diagonal matrix with blocks <math|C(f<rsub|1>),\<ldots\>,C(f<rsub|n>)> for
  monic polynomials <math|f<rsub|1>\<mid\>\<cdots\>\<mid\>f<rsub|n>>. In
  particular, the above says that every matrix is similar to a matrix in
  rational canonical form.

  <\remark>
    Although we shall not prove it, if two matrices in rational canonical
    form are similar then they are equal.
  </remark>

  <\example>
    For <math|f(X)=(X\<minus\>\<lambda\><rsub|1>)<rsup|d<rsub|1>>\<cdots\>(X\<minus\>\<lambda\><rsub|n>)<rsup|d<rsub|n>>>
    with <math|\<lambda\><rsub|1>,\<ldots\>,\<lambda\><rsub|n>> pairwise
    distinct and <math|d<rsub|1>+\<cdots\>+d<rsub|n>=n>, we have

    <\equation*>
      D(f)\<sim\><rsub|\<cal-E\>>D((X\<minus\>\<lambda\><rsub|1>)<rsup|d<rsub|1>>
      )\<varoplus\>\<cdots\>\<varoplus\>D((X\<minus\>\<lambda\><rsub|n>)<rsup|d<rsub|n>>).
    </equation*>

    To see this, we use induction on <math|r> to show that

    <\equation*>
      D((X\<minus\>\<lambda\><rsub|1>)<rsup|d<rsub|1>>
      )\<varoplus\>\<cdots\>\<varoplus\>D((X\<minus\>\<lambda\><rsub|n>)<rsup|d<rsub|n>>)\<sim\><rsub|\<cal-E\>>D(f<rsub|r>)\<varoplus\>D((X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>)\<varoplus\>\<cdots\>\<varoplus\>D((X\<minus\>\<lambda\><rsub|n>)<rsup|d<rsub|n>>)
    </equation*>

    where <math|f<rsub|r>(X)=(X\<minus\>\<lambda\><rsub|r>)<rsup|d<rsub|r>>f<rsub|r\<minus\>1>(X)>
    and <math|f<rsub|0>(X)=1>. This is certainly true when <math|r=0>, and
    for the inductive step when <math|r\<less\>n> note that the ideal
    generated by <math|f<rsub|r>> and <math|(X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>>
    is principal, say generated by <math|g<rsub|r>>. If <math|g<rsub|r>> has
    a root then it is a root of <math|(X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>>
    and also of <math|f<rsub|r>>, hence <math|g<rsub|r>> has no root and
    <math|\<langle\>f<rsub|r>\<rangle\>+\<langle\>(X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>\<rangle\>=\<langle\>1\<rangle\>>.
    By Lemma 6.10 we can replace the first element on the diagonal \U that is
    <math|f<rsub|r>> \U by <math|f<rsub|r>(X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>=f<rsub|r+1>>,
    and the <math|(deg f<rsub|r>+1)>st element on the diagonal \U that is
    <math|(X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>> by 1. The
    resulting matrix has <math|(deg f<rsub|r>)\<minus\>1+d<rsub|r+1>=(deg
    f<rsub|r+1>)\<minus\>1> copies of 1 on the diagonal after the initial
    <math|f<rsub|r+1>>, and hence equals <math|D(f<rsub|r+1>)\<varoplus\>D((X\<minus\>\<lambda\><rsub|r+1>)<rsup|d<rsub|r+1>>)\<varoplus\>\<cdots\>\<varoplus\>D((X\<minus\>\<lambda\><rsub|n>)<rsup|d<rsub|n>>)>.
    The example is complete.
  </example>

  <\theorem>
    Suppose that <math|A\<in\>M<rsub|n>(\<bbb-C\>)>. Then there are
    <math|\<lambda\><rsub|1>,\<ldots\>,\<lambda\><rsub|n>\<in\>\<bbb-C\>> and
    <math|t<rsub|1>,\<ldots\>,t<rsub|n>\<in\>\<bbb-N\><rsub|0>> with
    <math|t<rsub|1>+\<cdots\>+t<rsub|n>=n> such that
    <math|A\<sim\><rsub|\<cal-E\>>J(\<lambda\><rsub|1>,t<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>J(\<lambda\><rsub|n>,t<rsub|n>)>.
  </theorem>

  <\proof>
    By Theorem 6.6 there are polynomials <math|f<rsub|1>,\<ldots\>,f<rsub|n>>
    such that <math|X.I<rsub|n>\<minus\>A\<sim\><rsub|\<cal-E\>>\<#2206\>(X)>
    where <math|\<#2206\>(X)> is the diagonal matrix with entries
    <math|f<rsub|1>,\<ldots\>,f<rsub|n>>. As in the proof of Theorem 7.8 we
    conclude that we may suppose each <math|f<rsub|i>> is monic and write
    <math|d<rsub|i>> for its degree, and <math|n=d<rsub|1>+\<cdots\>+d<rsub|n>>.
    By permuting columns and rows as necessary we have
    <math|\<#2206\>(X)\<sim\><rsub|\<cal-E\>>D(f<rsub|1>)\<varoplus\>\<cdots\>\<varoplus\>D(f<rsub|n>)>.

    If <math|f\<in\>\<bbb-C\>[X]> is irreducible then
    <math|f(X)\<sim\>X\<minus\>\<lambda\>> for some
    <math|\<lambda\>\<in\>\<bbb-C\>> \U this is where we use the fact that
    the field is the complex numbers rather than a more general field \U so
    since <math|\<bbb-C\>[X]> is a Factorisation domain, we conclude that
    <math|f<rsub|i>(X)=(X\<minus\>\<lambda\><rsub|i,1>)<rsup|d<rsub|i,1>>\<cdots\>(X
    \<minus\>\<lambda\><rsub|i,r<rsub|i>>)<rsup|d<rsub|i,r><rsub|i>>> with
    <math|\<lambda\><rsub|i,1>,\<ldots\>,\<lambda\><rsub|i,r<rsub|i>>>
    pairwise distinct and <math|d<rsub|i,1>+\<cdots\>+d<rsub|i,r<rsub|i>>=d<rsub|i>>.
    In view of the calculation in Examples 7.7 & 7.10 we have

    <\align*>
      <tformat|<table|<row|<cell|D(f<rsub|i>)>|<cell|<math|>\<sim\><rsub|\<cal-E\>>D((X\<minus\>\<lambda\><rsub|i,1>)<rsup|d<rsub|i,1>>)\<varoplus\>\<cdots\>\<varoplus\>D((X\<minus\>\<lambda\><rsub|i,r<rsub|i>>)<rsup|d<rsub|i,r<rsub|i>>>)>>|<row|<cell|>|<cell|\<sim\><rsub|\<cal-E\>>(X.I<rsub|d<rsub|i,1>>\<minus\>J(\<lambda\><rsub|i,1>,d<rsub|i,1>))\<varoplus\>\<cdots\>\<varoplus\>(X.I<rsub|d<rsub|i,r<rsub|i>>>\<minus\>J(\<lambda\><rsub|i,r<rsub|i>>,d<rsub|i,r<rsub|i>>))>>>>
    </align*>

    Finally, let <math|\<lambda\><rsub|1>,\<ldots\>,\<lambda\><rsub|n>> be
    <math|\<lambda\><rsub|1,1>,\<ldots\>,\<lambda\><rsub|1,r<rsub|1>>,\<lambda\><rsub|2,1>,\<ldots\>,\<lambda\><rsub|2,r<rsub|2>>,\<ldots\>,\<lambda\><rsub|n,1>,\<ldots\>,\<lambda\><rsub|n,r<rsub|n>>>
    in order and similarly for <math|t<rsub|1>,\<ldots\>,t<rsub|n>>. The
    result is proved by Proposition 7.5.
  </proof>

  A matrix is said to be in <strong|Jordan normal form> if it is a block
  diagonal matrix with blocks <math|J(\<lambda\><rsub|1>,d<rsub|1>),\<ldots\>,J(\<lambda\><rsub|n>,d<rsub|n>)>
  for <math|\<lambda\><rsub|1>,\<ldots\>,\<lambda\><rsub|n>\<in\>\<bbb-F\>>
  and <math|d<rsub|1>,\<ldots\>,d<rsub|n>\<in\>\<bbb-N\><rsub|0>>. In
  particular, the above theorem says that every matrix over <math|\<bbb-C\>>
  is similar to a matrix in Jordan normal form.

  \;

  References

  [Ber14] D. Berlyne. Ideal theory in rings (Translation of \PIdealtheorie in
  Ringbereichen\Q by Emmy Noether). 2014, arXiv:1401.2577.

  [CNT19] C. J. Conidis, P. P. Nielsen, and V. Tombs. Transfinitely valued
  euclidean domains have arbitrary indecomposable order type. Communications
  in Algebra, 47(3):1105\U1113, 2019. doi:10.1080/00927872.2018.1501569.

  [Coh66] P. M. Cohn. On the structure of the GL2 of a ring. Inst. Hautes
  Etudes Sci. \A Publ. Math., (30):5\U53, 1966.
  <hlink|URL|http://www.numdam.org/item?id=PMIHES_1966__30__5_0>

  [Con] K. Conrad. Remarks about Euclidean domains.
  <hlink|URL|https://kconrad.math.uconn.edu/blurbs/ringtheory/euclideanrk.pdf>

  [Fuc58] L. Fuchs. Abelian groups. Publishing House of the Hungarian Academy
  of Sciences, Budapest, 1958.

  [Gra74] A. Grams. Atomic rings and the ascending chain condition for
  principal ideals. Proc. Cambridge Philos. Soc., 75:321\U329, 1974.
  doi:10.1017/s0305004100048532.

  [Hel43] O. Helmer. The elementary divisor theorem for certain rings without
  chain condition. Bull. Amer. Math. Soc., 49(4):225\U236, 04 1943.
  <hlink|URL|https://projecteuclid.org:443/euclid.bams/1183505099>

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
    <associate|auto-14|<tuple|7|?>>
    <associate|auto-15|<tuple|7.1|?>>
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

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Applications
      of Smith normal form> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14><vspace|0.5fn>

      <with|par-left|<quote|1tab>|7.1<space|2spc>Matrix forms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>
    </associate>
  </collection>
</auxiliary>