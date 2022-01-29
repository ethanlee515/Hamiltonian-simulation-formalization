%{

Require Import String.
Require Import HSF_Syntax.
Require Import Reals.
Require Import PauliRotations.

%}

%token<R> REALVAL

%token<string> ID

%token EOF DOT LEFTBRAC RIGHTBRAC COLON PLUS SUBTR DIVIDE SEMICOLON SITE HAM HSF ENDHSF XTOK YTOK ZTOK ITOK

%type<H_Program> h_program

%type<list string> declarations

%type<list HSF_Term> instructions

%type<HSF_Term> instruction

%type<list TIH_Term> tih

%type<list TIH_Term> tih_rest

%type<TIH_Term> tih_term

%type<list HPauli> hPaulis1

%type<list HPauli> hPaulis

%type<HPauli> hPauli

%start<H_Program> h_program_top

%%

h_program_top:
| prog=h_program EOF
{ prog }

h_program:
| HSF progname=ID SITE decls=declarations HAM insts=instructions ENDHSF
{makeHProg decls insts}

declarations:
|
{ nil }
| s=ID rest=declarations
{ s::rest }

instructions:
|
{ nil }
| inst=instruction rest=instructions
{ inst :: rest }

instruction:
| LEFTBRAC termid=ID COLON duration=REALVAL SEMICOLON ham=tih RIGHTBRAC
{ makeHSF_Term termid (HScReal duration "?") ham }

tih:
| t=tih_term r=tih_rest
{ t :: r }

tih_rest:
|
{ nil }
| PLUS t=tih_term r=tih_rest
{ t :: r}

tih_term:
| scale_val=REALVAL hp=hPaulis1
{ makeTIH_Term (HScReal scale_val "?") hp }
| hp=hPaulis1
{ makeTIH_Term (HScReal (INR 1) "1") hp }

hPaulis1:
| head=hPauli tail=hPaulis
{ head :: tail }

hPaulis:
|
{ nil }
| head=hPauli tail=hPaulis
{ head :: tail }

hPauli:
| loc=ID DOT XTOK
{ HIdOp loc Pauli_X }
| loc=ID DOT YTOK
{ HIdOp loc Pauli_Y }
| loc=ID DOT ZTOK
{ HIdOp loc Pauli_Z }
| loc=ID DOT ITOK
{ HIdOp loc Pauli_I }
