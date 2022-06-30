# Examples of axial algebras of Monster type $(\alpha, \beta)$

Magma code for examples of axial algebras of Monster type.

Currently the symmetric 2-generated primitive axial algebras of Monster type $(\alpha, \beta)$.  These were classified by Yabe (2020), with the characteristic 5 case covered by Franchi and Mainardis (2021), and the quotients of the Highwater algebra and its cover described explicitly by Franchi, Mainardis and McInroy (2022).

Note that we do not use Yabe's notation, but instead use the notation of Shpectorov and McInroy, see the files for details.

## Getting started

Begin by cloning the repository by running

    git clone https://github.com/JustMaths/AxialMonsterType
    
or

    git clone git@github.com:JustMaths/AxialMonsterType.git
    
Now, when you are in the AxialMonsterType directory start Magma and attach the spec file

    AttachSpec("2-gen Monster.spec");
    
## Get some algebras

Since intrinsics can't start with a number in Magma, we put an `M` in front of the algebra name.  For example, to get the $3\mathrm{A}$ algebra type:

    A, gens, frob := M3A();
    
Here `A` is the algebra over the function field, `gens` is an indexed set of generators and `frob` is a Frobenius form.  If you know the parameters you want you can call that directly by typing

    A, gens, frob := M3A(1/4, 1/32);
    
to get the Norton-Sakuma algebra $3\mathrm{A}(\frac{1}{4}, \frac{1}{32})$.
