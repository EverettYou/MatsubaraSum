(* ::Package:: *)

(* Mathematica Package *)

(* Created by the Wolfram Workbench 2010-12-2 *)
(* :Name: MatsubaraSum` *)
(* :Title: Matsubara Summation Package *)
(* :Author: Everett You *)
(* :Summary:
	The MatsubaraSum package provides the function
	MatsubaraSum to analytically evaluate the Matsubara
	frequency summation of fractionals over imaginary 
	frequencies. Both analytic or numeric evaluation with
	or without given temperature are supported. 
*)
(* :Context: MatsubaraSum` *)
(* :Package Version: 1.0 *)
(* :Copyright: *)
(* :History:
	Originally written by Everett You, 2009.
*)
(* :Keywords: functional derivatives, calculus of variations, first integrals,
	Ritz variational method
*)
(* :Source: None. *)
(* :Warnings: None. *)
(* :Mathematica Version: 2.1 *)
(* :Limitations:
	Only fractional expressions can be handeled. 
*)
(* :Discussion: *)

BeginPackage["MatsubaraSum`"]
(* Exported symbols added here with SymbolName::usage *) 
MatsubaraSum::usage="MatsubaraSum[\*StyleBox[\"expr\",\"TI\"],\*StyleBox[\"z\", \"TI\"]] evaluates the Matsubara \
summation of \*StyleBox[\"expr\", \"TI\"] over the imaginary \
frequency \*StyleBox[\"z\", \"TI\"].\nMatsubaraSum[\*StyleBox[\"expr\", \"TI\"],\*StyleBox[\"z\", \"TI\"],\[Beta]] with the inversed temperature \[Beta] given.";
WeightingFunction::usage="WeightingFunction is an option for \
MatsubaraSum that specifies the weighting \
function. The following settings can be used: \
Both, Fermionic, Bosonic, or a pure function. ";
Both::usage="Both is a setting used for the WeightingFunction option. ";
Fermionic::usage="Fermionic is a setting used for the WeightingFunction option. ";
Bosonic::usage="Bosonic is a setting used for the WeightingFunction option. ";
ControlledPlane::usage="ControlledPlane is an option for MatsubaraSum \
that specifies which half plane is to be \
controlled for convergence. The following \
settings can be used: Left, Right, or All. ";
$StatisticalSign::usage="$StatisticalSign specifies the statistical sign. ";
DistributionFunction::usage="DistributionFunction[\[Xi]] represents the generic \
distribution function.\nDistributionFunction[\[Eta],\[Xi]] specifies \
the statistical sign \[Eta].";
BosonicFrequencies::usage="BosonicFrequencies represents \
the domain of bosonic frequencies. ";
FermionicFrequencies::usage="FermionicFrequencies represents \
the domain of fermionic frequencies. ";
Begin["`Private`"]
(* Implementation of the package *)

Options[Res]:={AccuracyGoal->10};
Res[expr_, {z_, z0_}, OptionsPattern[Res]] :=
	Module[{acc, ZeroQ, \[Delta], R1, R},
		acc = OptionValue[AccuracyGoal];
		ZeroQ = 
			PossibleZeroQ[#1] || NumericQ[#1] && Chop[#1, 10^-(#2 acc)] == 0 &;
		R1 = Simplify[Chop[Together[\[Delta] expr /. z -> z0 + \[Delta]], 10^-acc]];
		R[Rp_, m_] := Module[{Rm},
			Rm = Simplify[Chop[Together[((m - 1) Rp + \[Delta] D[Rp, \[Delta]])/m], 10^-acc]];
     		If[ZeroQ[Denominator[Rm] /. \[Delta] -> 0, m], R[Rm, m + 1], 
      		Rm /. \[Delta] -> 0]
     		];
   		If[ZeroQ[Denominator[R1] /. \[Delta] -> 0, 1], R[R1, 2], 
    		R1 /. \[Delta] -> 0]
   ];
	

$StatisticalSign = Global`\[Eta];
Options[MatsubaraSum]:={WeightingFunction->Both,ControlledPlane->Right};
SyntaxInformation[MatsubaraSum]={"ArgumentsPattern"->{_,__,OptionsPattern[]},"LocalVariables"->{"Solve",{2,2}}};

MatsubaraSum[expr_,z_,OptionsPattern[MatsubaraSum]]:=
	Module[{presum,den,WF},
		presum=Together[expr];
		den=DeleteCases[Denominator[presum],_?(!PolynomialQ[#,z]&)];
		WF[type_]:=With[{slst=Switch[OptionValue[ControlledPlane],Left,{-1},Right,{+1},All,{-1,1}]},
			Switch[type,
				Both,Mean[$StatisticalSign # DistributionFunction[$StatisticalSign,# z]&/@slst],
				Fermionic,Mean[-# DistributionFunction[-1,# z]&/@slst],
				Bosonic,Mean[# DistributionFunction[+1,# z]&/@slst],
				_,type]];
		-Normal[RootSum[Evaluate[den/.z->#]&,Res[presum WF@@Flatten[{OptionValue[WeightingFunction]}],{z,#}]&]]
];

MatsubaraSum[expr_,z_,\[Beta]_,OptionsPattern[MatsubaraSum]]:=
	Module[{presum,den,WF},
		presum=Together[expr];
		den=DeleteCases[Denominator[presum],_?(!PolynomialQ[#,z]&)];
		Options[WF]={ControlledPlane->Left};
		WF[type_,OptionsPattern[WF]]:=With[{slst=Switch[OptionValue[ControlledPlane],Left,{-1},Right,{+1},All,{-1,1}]},
			Switch[type,
				Both,Mean[$StatisticalSign #/(Exp[# \[Beta] z]-$StatisticalSign)&/@slst],
				Fermionic,Mean[-#/(Exp[# \[Beta] z]+1)&/@slst],
				Bosonic,Mean[# /(Exp[# \[Beta] z]-1)&/@slst],
				_,type]];
		-Normal[RootSum[Evaluate[den/.z->#]&,Res[presum WF@@Flatten[{OptionValue[WeightingFunction]}],{z,#}]&]]
];

FermionicFrequencies = {Global`i\[Omega]};
BosonicFrequencies = {Global`i\[Nu]};
BosonicQ[z_] := MemberQ[BosonicFrequencies,z];
FermionicQ[z_] := MemberQ[FermionicFrequencies,z];

SimplifyDistributionFunction[expr_]:=
expr//.
{$StatisticalSign^2->1,
DistributionFunction[Times[-1,\[Xi]_]]:>
	-$StatisticalSign-DistributionFunction[\[Xi]],
DistributionFunction[\[Eta]_,Times[-1,\[Xi]_]]:>
	-\[Eta]-DistributionFunction[\[Eta],\[Xi]],
DistributionFunction[\[Eta]_,z_?BosonicQ]:>
	DistributionFunction[\[Eta],0],
DistributionFunction[\[Eta]_,z_?FermionicQ]:>
	-DistributionFunction[-\[Eta],0],
DistributionFunction[\[Eta]_,z_?BosonicQ+\[Xi]_]:>
	DistributionFunction[\[Eta],\[Xi]],
DistributionFunction[\[Eta]_,z_?FermionicQ+\[Xi]_]:>
	-DistributionFunction[-\[Eta],\[Xi]],
DistributionFunction[\[Eta]_,-z_?BosonicQ+\[Xi]_]:>
	DistributionFunction[\[Eta],\[Xi]],
DistributionFunction[\[Eta]_,-z_?FermionicQ+\[Xi]_]:>
	-DistributionFunction[-\[Eta],\[Xi]]};
SetOptions[Simplify,TransformationFunctions->{Automatic,SimplifyDistributionFunction}];
SetOptions[FullSimplify,TransformationFunctions->{Automatic,SimplifyDistributionFunction}];
End[]
SetAttributes[{MatsubaraSum,DistributionFunction},{ReadProtected}];
EndPackage[]

Notation`AutoLoadNotationPalette=False;
Get["Notation`"];
Notation[\!\(\*
TagBox[
RowBox[{
SubscriptBox["n", "B"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{"DistributionFunction", "[", 
RowBox[{"1", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubscriptBox["n", "F"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{"DistributionFunction", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubscriptBox["n", "\[Eta]_"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{"DistributionFunction", "[", 
RowBox[{"\[Eta]_", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "B", "\[Prime]"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "1"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{"1", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "F", "\[Prime]"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "1"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "\[Eta]_", "\[Prime]"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "1"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{"\[Eta]_", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "B", "\[DoublePrime]"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "2"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{"1", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "F", "\[DoublePrime]"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "2"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "\[Eta]_", "\[DoublePrime]"], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "2"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{"\[Eta]_", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "B", 
TagBox[
RowBox[{"(", "k_", ")"}],
Derivative],
MultilineFunction->None], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "k_"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{"1", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "F", 
TagBox[
RowBox[{"(", "k_", ")"}],
Derivative],
MultilineFunction->None], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "k_"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];
Notation[\!\(\*
TagBox[
RowBox[{
SubsuperscriptBox["n", "\[Eta]_", 
TagBox[
RowBox[{"(", "k_", ")"}],
Derivative],
MultilineFunction->None], "[", "x_", "]"}],
"NotationTemplateTag"]\) \[DoubleLongLeftRightArrow] \!\(\*
TagBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", 
RowBox[{"0", ",", "k_"}], "]"}], "[", "DistributionFunction", "]"}], "[", 
RowBox[{"\[Eta]_", ",", "x_"}], "]"}],
"NotationTemplateTag"]\)];









