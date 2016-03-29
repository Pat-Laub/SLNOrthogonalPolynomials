(* ::Package:: *)

(************Functions relating to moments of the SLN distribution and others.****************)
(*First central moments of SLN.*)
SLNMean[\[Mu]_,\[CapitalSigma]_]:=Total[Exp[\[Mu]+Diagonal[\[CapitalSigma]]/2]];
SLNVariance[\[Mu]_,\[CapitalSigma]_]:=Total[Table[Exp[\[Mu][[i]]+\[Mu][[j]]+(\[CapitalSigma][[i,i]]+\[CapitalSigma][[j,j]])/2]*(Exp[\[CapitalSigma][[i,j]]]-1),{i,Length[\[Mu]]},{j,Length[\[Mu]]}],2];

(*The k-th moment of the sum of n independent lognormals.*)
SLNIndependentMoments[\[Mu]_,\[CapitalSigma]_,k_]:=Module[{Summand,AllIndices},Summand[inds_]:=(Multinomial@@inds)*Exp[Total[inds*\[Mu]+(1/2)*inds^2*Diagonal[\[CapitalSigma]]]];
AllIndices[n_,kk_]:=Flatten[Permutations[PadRight[#,n]]&/@IntegerPartitions[kk,n],1];
Total[Summand/@AllIndices[Length[\[Mu]],k]]];

(*Left tail slope of F(x) for SLN (follow the steps of Tankov).*)
SLNLeftSlope[\[CapitalSigma]_]:=Module[{n,w,wBar,wPos,IBar,nBar,B,BBar,BBarSum},n=Length[\[CapitalSigma]];B=Inverse[\[CapitalSigma]];
w=Array[ww,n];
wBar=w/.Last[NMinimize[{w.B.w,Total[w]==1},w]];
(*Extract the positive elements.*)wPos=Table[wBar[[i]]>0,{i,n}];
IBar=Flatten[Position[wPos,True]];
nBar=Length[IBar];
(*Create the subsampled inverse covariance matrix.*)BBar=B[[IBar,IBar]];
BBarSum=Total[BBar,2];
Sqrt[BBarSum]];

(*Useful functions and constants.*)
\[Phi][x_]:=CDF[NormalDistribution[],x];
linspace[s_,f_,n_]:=Range[s,f,(f-s)/(n-1)]
\[Xi]=Log[10]/10;

(*Functions relating to the log skew normal distribution.*)
(*Left tail slope of F(x) for LSKN.*)
LSKNLeftSlope[\[Lambda]_,\[Omega]_]:=Sqrt[1+\[Lambda]^2]/\[Omega];

(*First central moments of of LSKN.*)
LSKNMean[\[Beta]_,\[Epsilon]_,\[Omega]_]:=2 Exp[\[Epsilon]+\[Omega]^2/2]*\[Phi][\[Beta]*\[Omega]];
LSKNVariance[\[Beta]_,\[Epsilon]_,\[Omega]_]:=2 Exp[2 \[Epsilon]+\[Omega]^2]*(Exp[\[Omega]^2]*\[Phi][2 \[Beta]*\[Omega]]-2 \[Phi][\[Beta]*\[Omega]]^2);


(*The LSKN distribution.*)
LogSkewNormalDistribution[\[Mu]_,\[Sigma]_,\[Alpha]_] := TransformedDistribution[Exp[xxx],xxx\[Distributed]SkewNormalDistribution[\[Mu],\[Sigma],\[Alpha]]];

(*****************************************Normal estimators of the density*******************************************)
(*Numerically integrate the convolution equation (for n\[LessEqual]4 or so). *)
MultiLNPDF[\[Mu]_,\[CapitalSigma]_,xs_]:=(rvs=Array[rv,Round[Length[\[Mu]]]];
PDF[TransformedDistribution[Exp[rvs],rvs\[Distributed]MultinormalDistribution[\[Mu],\[CapitalSigma]]],xs]);

CDFConvReg[s_,n_]:=(ys=Table[yy[i],{i,n}];ParametricRegion[{ys,Total[ys] <= s},Evaluate[Map[{#,0,s}&,ys]]]);
PDFConvReg[s_,n_]:=(ys=Table[yy[i],{i,n}];ParametricRegion[{ys,Total[ys] == s},Evaluate[Map[{#,0,s}&,ys]]]);

ConvolutionEstimator[\[Mu]_,\[CapitalSigma]_]:=Module[{n,x},
n=Length[\[Mu]]; x=Array[xx,n];
Function[{s},NIntegrate[(1/Sqrt[n])*MultiLNPDF[\[Mu],\[CapitalSigma],x],x\[Element]PDFConvReg[s,n],PrecisionGoal->If[n<4,4,4]]]];

GeneralConvolutionEstimator[Dist_]:=Module[{n,x},(*Print["Constructing ConvolutionEstimator."]; ,PrecisionGoal->8 *)
n=Length[Flatten[RandomVariate[Dist,1]]]; x=Array[xx,n];
Function[{s},NIntegrate[(1/Sqrt[n])*PDF[Dist,x],x\[Element]PDFConvReg[s,n],PrecisionGoal->If[n<4,4,4]]]];


ConvolutionCDFEstimator[\[Mu]_,\[CapitalSigma]_]:=Module[{n,x},
n=Length[\[Mu]]; x=Array[xx,n];
Function[{s},NIntegrate[MultiLNPDF[\[Mu],\[CapitalSigma],x],x\[Element]CDFConvReg[s,n],PrecisionGoal->If[n<4,8,4]]]];

(*Use the default kernel smooth density estimate.*)
KernelEstimator[SLNs_]:=Module[{},(*Print["Constructing KernelEstimator"];*)PDF[SmoothKernelDistribution[SLNs,Automatic,{"Bounded",{0,Infinity},"Gaussian"}]]];


(*Conditional Monte Carlo approach.*)
CondMCEstimator[\[Mu]_,\[CapitalSigma]_,Norms_,SLNs_]:=Module[{\[CapitalSigma]11,\[CapitalSigma]12,\[CapitalSigma]21,\[CapitalSigma]22,rep\[Mu],cond\[CapitalSigma],cond\[Mu]s,PDFLogNormal,SLNsMF},(*Print["Constructing CondMCEstimator."];*)(*Split up the covariance matrix to find the conditional standard deviation.*)\[CapitalSigma]11=\[CapitalSigma][[1,1]];\[CapitalSigma]12=\[CapitalSigma][[1,2;;]];
\[CapitalSigma]21=\[CapitalSigma][[2;;,1]];\[CapitalSigma]22=\[CapitalSigma][[2;;,2;;]];
cond\[CapitalSigma]=Sqrt[\[CapitalSigma]11-\[CapitalSigma]12.Inverse[\[CapitalSigma]22].\[CapitalSigma]21];
(*Find the conditional means (given the first column).*)rep\[Mu]=ConstantArray[\[Mu][[2;;]],Length[SLNs]];
cond\[Mu]s=\[Mu][[1]]+\[CapitalSigma]12.Inverse[\[CapitalSigma]22].(Transpose[Norms[[All,2;;]]-rep\[Mu]]);
(*Lognormal PDF (which will handle different means for each x value).*)(*N.B.We require xs to be a list now.*)PDFLogNormal=Function[{mu,sigma,xs},Table[Boole[xs[[i]]>0],{i,Length[xs]}]*Re[Exp[-(Log[xs]-mu)^2/(2*sigma^2)]/(xs*sigma*Sqrt[2 Pi])]];
(*We require S_n-Exp[X_1] values (read as "SLNs Minus First").*)SLNsMF=SLNs-Exp[Norms[[All,1]]];
(*Estimate the SLN PDF by the mean of this conditional 1D lognormal PDF.*)Function[{x},Mean[PDFLogNormal[cond\[Mu]s,cond\[CapitalSigma],x-SLNsMF]]]];

(*Basic Fenton-Wilkinson;moment matching a LN to SLN.*)
FentonWilkinsonEstimator[\[Mu]_,\[CapitalSigma]_]:=Module[{\[Mu]S,\[Sigma]S},{\[Mu]S,\[Sigma]S}=Flatten[{\[Mu]Val,\[Sigma]Val}/.Solve[{SLNMean[\[Mu],\[CapitalSigma]]==Mean[LogNormalDistribution[\[Mu]Val,\[Sigma]Val]],SLNVariance[\[Mu],\[CapitalSigma]]==Variance[LogNormalDistribution[\[Mu]Val,\[Sigma]Val]], \[Sigma]Val>0},{\[Mu]Val,\[Sigma]Val}, Reals]];
PDF[LogNormalDistribution[\[Mu]S,\[Sigma]S]]];


(*Log skew normal approximation;moment matching and slope matching.*)
LSKNEstimator[\[Mu]_,\[CapitalSigma]_]:=Module[{\[Beta]Opt,\[Epsilon]Opt,\[Lambda]Opt,\[Omega]Opt},
{\[Beta]Opt,\[Epsilon]Opt,\[Lambda]Opt,\[Omega]Opt}={\[Beta],\[Epsilon],\[Lambda],\[Omega]}/.FindRoot[{\[Beta]==\[Lambda]/Sqrt[1+\[Lambda]^2],(*\[Beta] is simply are nicer form of \[Lambda].*)SLNLeftSlope[\[CapitalSigma]]==LSKNLeftSlope[\[Lambda],\[Omega]],SLNMean[\[Mu],\[CapitalSigma]]==LSKNMean[\[Beta],\[Epsilon],\[Omega]],SLNVariance[\[Mu],\[CapitalSigma]]==LSKNVariance[\[Beta],\[Epsilon],\[Omega]]},{{\[Beta],1},{\[Epsilon],1},{\[Lambda],1},{\[Omega],1}}];
PDF[LogSkewNormalDistribution[\[Epsilon]Opt,\[Omega]Opt,\[Lambda]Opt]]];

(**************************************Polynomial approximations to the density**********************************)
(*Calculate the coefficients for the Hermite polynomial approximation (using recurrence relation).*)

HermiteCoefficients[RVs_,K_]:=Module[{x,a,H,HR},x=RVs/Sqrt[2];
a[0]=1;
H[1]=HermiteH[1,x];
a[1]=(2^(1/2)*Sqrt[Factorial[1]])^(-1)*Mean[H[1]];
H[2]=HermiteH[2,x];
a[2]=(2^(2/2)*Sqrt[Factorial[2]])^(-1)*Mean[H[2]];
(*H_{n}(x)=2x*H_{n-1}(x)\[Minus]2(n-1)H_{n\[Minus]2}(x).*)
Do[
	H[j+1]=2 x*H[j]-2 j*H[j-1];
	a[j+1]=(2^((j+1)/2)*Sqrt[Factorial[j+1]])^(-1)*Mean[H[j+1]],{j,2,K-1}];
Table[a[i],{i,0,K}]
];

(*Approximate f(x) using the the transformed Hermite polynomials.*)

HermiteEstimator[\[Mu]_,\[CapitalSigma]_,SLNs_,K_:25]:=Module[{n,CMC,LSLNs,L\[Mu],L\[Sigma],vars,LSLNsC,TransTargetDist,Polys,Coeffs,fTrans},(*Print["Constructing HermiteEstimator."];*)
n=Length[\[Mu]];CMC=!(2 <= n <= 4);
(*Transform them by their log and center the result.*)
LSLNs=Log[SLNs];

(* Numerically integrate to find Exp[log[S]]. *)
If[!CMC,
	vars=Array[var,n];
	L\[Mu]=NExpectation[Log[Total[E^vars]],vars\[Distributed]MultinormalDistribution[\[Mu],\[CapitalSigma]],PrecisionGoal->If[n<4,(4-(n-2)),2]];
	L\[Sigma]=Sqrt[NExpectation[(Log[Total[E^vars]]-L\[Mu])^2,vars\[Distributed]MultinormalDistribution[\[Mu],\[CapitalSigma]],PrecisionGoal->If[n<4,(4-(n-2)),2]]],
	(* Otherwise use CMC. *)
	L\[Mu]=Mean[LSLNs];
	L\[Sigma]=StandardDeviation[LSLNs]];

If[Length[\[CapitalSigma]]>0, L\[Sigma] = Max[{L\[Sigma], 1.01*Sqrt[(1/2)*Max[Diagonal[\[CapitalSigma]]]]}]];
Print["{K, L\[Mu], L\[Sigma]} = ",{K,L\[Mu],L\[Sigma]}];

LSLNsC = (LSLNs-L\[Mu])/L\[Sigma];

(*Fit this with Hermite polynomials and the standard normal reference distribution.*)
Coeffs=HermiteCoefficients[LSLNsC,K];
Polys=Function[{x},Table[(2^(i/2)*Sqrt[Factorial[i]])^(-1)*HermiteH[i,x/Sqrt[2]],{i,0,K}]];

(*Construct the density estimate for the transformed space.*)
fTrans=Function[{x},Total[Coeffs*Polys[x]]*PDF[NormalDistribution[],x]];
(*Create the transformed density estimate.*)
Function[{x},(x*L\[Sigma])^(-1)*fTrans[(Log[x]-L\[Mu])/L\[Sigma]]]];


(*HELPER FUNCTIONS FOR GAUSS-HERMITE QUADRATURE.*)
(*Directly from:http://math.stackexchange.com/questions/180447/can-i-only-apply-the-gauss-hermite-routine-with-an-infinite-interval-or-can-i-tr*)
(*Golub-Welsch algorithm*)
golubWelsch[d_?VectorQ,e_?VectorQ]:=Transpose[MapAt[(First[e] Map[First,#]^2)&,Eigensystem[SparseArray[{Band[{1,1}]->d,Band[{1,2}]->Sqrt[Rest[e]],Band[{2,1}]->Sqrt[Rest[e]]},{Length[d],Length[d]}]],{2}]];

(*generate nodes and weights for Gauss-Hermite quadrature*)
ghq[n_Integer,prec_: MachinePrecision]:=Transpose[Sort[golubWelsch[ConstantArray[0,n],N[Prepend[Range[n-1]/2,Sqrt[Pi]],prec]]]];

(*Calculate moments of the exponentially tilted SLN using Gauss-Hermite quadrature.*)
LiGaussHermite[i_,\[Theta]_,\[Mu]_,\[CapitalSigma]_,GHOrderInit_:64]:=Module[{n,GHOrder,\[CapitalSigma]Inv,\[CapitalSigma]Half,h,x,x\[Prime],H,HInv,first,v,GH,xi,wi,inds},(*Some constants.*)
n=Length[\[Mu]];GHOrder=Max[GHOrderInit/2^(n-2), 4];
\[CapitalSigma]Inv=Inverse[\[CapitalSigma]];\[CapitalSigma]Half=MatrixPower[\[CapitalSigma],1/2];

(*Function in the exponent.*)h[x_]:=-i*Log[Total[Exp[\[Mu]+x]]]+\[Theta]*Total[Exp[\[Mu]+x]]+(1/2)*x.\[CapitalSigma]Inv.x;
(*Calculate the minimiser.*)x=Array[xx,n];
x\[Prime]=Flatten[{x}/.Last[Quiet[FindMinimum[h[x],x]]]];
(*Construct the approximation.*)H=i*Outer[Times,Exp[\[Mu]+x\[Prime]],Exp[\[Mu]+x\[Prime]]]/(Total[Exp[\[Mu]+x\[Prime]]]^2)+\[CapitalSigma]Inv-DiagonalMatrix[\[CapitalSigma]Inv.x\[Prime]];
(*If[n > 4, Return[Exp[-h[x\[Prime]]]/Sqrt[Det[\[CapitalSigma].H]]]];*)
first=SetPrecision[Exp[-h[x\[Prime]]],Infinity];(* /Sqrt[Det[\[CapitalSigma].H]] and*Sqrt[Det[\[CapitalSigma].H]]*)(*I_i.*)v[z_]:=Exp[i*Log[Total[Exp[\[Mu]+x\[Prime]+z]]]-\[Theta]*Total[Exp[\[Mu]+x\[Prime]+z]]-x\[Prime].\[CapitalSigma]Inv.z];
GH=ghq[GHOrder,20];
xi=GH[[1,;;]];wi=GH[[2,;;]];
inds=Tuples[Range[1,GHOrder],n];
(*TODO:Underflow below sometimes.*)first*v[ConstantArray[0,n]]^(-1)*(Pi)^(-n/2)*Total[Map[(Times@@wi[[#]])*v[\[CapitalSigma]Half.(Sqrt[2]*xi[[#]])]&,inds]]];

(* Use standard CMC. *)
LiCMC[i_,\[Theta]_,SLNs_] := Mean[(SLNs^i)*Exp[-\[Theta]*SLNs]];

Li[i_,\[Theta]_,\[Mu]_,\[CapitalSigma]_,SLNs_,CMC_] :=
	If[CMC,
		LiCMC[i,\[Theta],SLNs],
		LiGaussHermite[i,\[Theta],\[Mu],\[CapitalSigma]]];

(*Calculate the coefficients for the Laguerre polynomial approximation.*)
LaguerreCoefficientsGH[K_,\[Theta]_,L_,r_,m_,\[Mu]_,\[CapitalSigma]_]:=Module[{ExpTiltedMoments,Coeffs,Qn,QnCoeffs},
ExpTiltedMoments=Table[LiGaussHermite[i,\[Theta],\[Mu],\[CapitalSigma]],{i,1,K}];
Coeffs=ConstantArray[0,K];
Qn[x_,i_]:=(-1)^i*Binomial[i+r-1,i]^(-1/2)*LaguerreL[i,r-1,x/m];
Do[
QnCoeffs=CoefficientList[Qn[xxx,i],xxx];
Coeffs[[i]]=QnCoeffs[[1]]+(1/L)*Total[QnCoeffs[[2;;]]*ExpTiltedMoments[[;;i]]],{i,1,K}];
Coeffs];

(*Calculate the coefficients for the Laguerre polynomial approximation.*)
(*TODO:Redo using recurrence relation... perhaps.*)
LaguerreCoefficientsCMC[\[Theta]_,L_,SLNs_,Polys_]:= Mean[Map[Exp[-\[Theta]*#]*Polys[#]&,SLNs]]/L;

(*Construct the Laguerre/Gamma polynomial expansion.*)
(*N.b.This doesn't use the SLNs MC simulations.(CHECK LATER!)*)

LaguerreEstimator[\[Mu]_,\[CapitalSigma]_,SLNs_,K_:25]:=Module[{n,CMC,TiltExp,TiltVar,maxr,min,r,m,\[Theta],L,Coeffs,Polys,\[Epsilon]},
n=Length[\[Mu]]; CMC= !(2 <= n <= 4); \[Theta]=If[n > 4, 2, 1];

L=Li[0,\[Theta],\[Mu],\[CapitalSigma],SLNs,CMC];
TiltExp=Li[1,\[Theta],\[Mu],\[CapitalSigma],SLNs,CMC]/L;
TiltVar=Li[2,\[Theta],\[Mu],\[CapitalSigma],SLNs,CMC]/L - TiltExp^2;
maxr = If[n <= 4, 10, 100];
(* Can't go 1/(2\[Theta]) + \[Epsilon] < m < 1/\[Theta] - \[Epsilon], so use p=m-1/(2\[Theta])-\[Epsilon] ie m=p+1/(2\[Theta]) and 0 < p < 1/(2\[Theta]) - 2\[Epsilon] *)
\[Epsilon]=1/(100*2\[Theta]);
min=NMinimize[{((TiltExp-rVal*(pVal+1/(2\[Theta])))/TiltExp)^2 + ((TiltVar-rVal*(pVal + 1/(2 \[Theta]) + \[Epsilon])^2)/TiltVar)^2,
	rVal > 0, rVal <= maxr, 0 <= pVal, pVal <= 1/(2*\[Theta]) - 2*\[Epsilon]},{rVal,pVal},
	MaxIterations->10^3, PrecisionGoal->3];
{r,m}=min[[2,;;,2]] + {0, 1/(2\[Theta])+\[Epsilon]};
Print["{K,r,m,\[Theta]} = ",{K,r,m,\[Theta]}, " Min = ", First[min]];

(*Construct the orthonormal polynomials.*)
Polys=Function[{x},Table[(-1)^i*Binomial[i+r-1,i]^(-1/2)*LaguerreL[i,r-1,x/m],{i,1,K}]];

(*Construct the a_n coefficients.*)
Coeffs=If[CMC,
	LaguerreCoefficientsCMC[\[Theta],L,SLNs,Polys],
	LaguerreCoefficientsGH[K,\[Theta],L,r,m,\[Mu],\[CapitalSigma]]];

(*Construct the density estimate for the transformed space.*)
Function[{x},Exp[\[Theta]*x]*L*(1+Total[Coeffs*Polys[x]])*PDF[GammaDistribution[r,m],x]]
];
	
(***************************************************Error functions************************************************)
(*Calculate the L1 errors of the approximate p.d.f.s against the target p.d.f.*)

L1Errors[TargetPDF_,ApproxPDFs_,start_,end_]:=Module[{F},F[f_]:=Quiet[NIntegrate[Abs[TargetPDF[x]-f[x]],{x,start,end},AccuracyGoal->4,PrecisionGoal->4,Method->{"TrapezoidalRule","RombergQuadrature"->True,"SymbolicProcessing"->0}]];
Map[F,ApproxPDFs]];

(*Calculate the L2 errors of the approximate p.d.f.s against the target p.d.f.*)
L2Errors[TargetPDF_,ApproxPDFs_,start_?NumericQ,end_?NumericQ]:=
Map[Quiet[Sqrt[NIntegrate[(TargetPDF[x]-#[x])^2,{x,start,end},AccuracyGoal->4,PrecisionGoal->4,Method->{"TrapezoidalRule","RombergQuadrature"->True,"SymbolicProcessing"->0}]]] &,ApproxPDFs];

SupNormErrors[TargetPDF_,ApproxPDFs_,start_,end_]:=
Map[Quiet[First[FindMaximum[{Abs[TargetPDF[x]-#[x]],start<=x<=end},{x,1}]]]&,ApproxPDFs];

(*************************************************Final testing procedure*****************************************)

AssessEstimators[\[Mu]_,\[CapitalSigma]_,R_,plotName_,Ks_:{25,16},Verbose_: True]:=Module[{n,P,\[Rho],Norms,SLNs,QNorms,QSLNs,fConv,fFW,fLSKN,fCondMC,fCondMCQ,fHermite,fHermiteQ,fLaguerre,fKS,fLaguerreCMC,r1,r2,q1,q2,res,DensPlot,ErrPlot,LegList},(*Generate some random variables for a particular set of parameters.*)(*We will use these common random numbers for all algorithms.*)
n=Length[\[Mu]];
If[Verbose,Print["Generating common random variables."]];

SeedRandom[1];
Norms=RandomVariate[MultinormalDistribution[\[Mu],\[CapitalSigma]],R];
SLNs=Total[Transpose[Exp[Norms]]];

(*Create all the estimators.*)
If[Verbose,Print["Creating the different estimators."]];
q2=SLNMean[\[Mu],\[CapitalSigma]];
If[n<= 4,
	fConv[x_]:=fConv[x]=ConvolutionEstimator[\[Mu],\[CapitalSigma]][x];
	If[Verbose,Print["f(1) = ",N[fConv[1]]]]
];

If[Verbose,Print["Number of fConv[_] stored: ",Length[DownValues[fConv]]]];

fFW = FentonWilkinsonEstimator[\[Mu],\[CapitalSigma]];
If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(FW\)]\)(1) = ",N[fFW[1]]]];
fLSKN=LSKNEstimator[\[Mu],\[CapitalSigma]];
	If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(Sk\)]\)(1) = ",N[fLSKN[1]]]];
fCondMC=CondMCEstimator[\[Mu],\[CapitalSigma],Norms,SLNs];
If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(Cond\)]\)(1) = ",N[fCondMC[1]]]];
fHermite=HermiteEstimator[\[Mu],\[CapitalSigma],SLNs,Ks[[1]]];
If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(N\)]\)(1) = ",N[fHermite[1]]]];
fLaguerre=LaguerreEstimator[\[Mu],\[CapitalSigma],SLNs,Ks[[2]]];
If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(\[CapitalGamma]\)]\)(1) = ",N[fLaguerre[1]]]];

(*Make some plots.*)
If[Verbose,Print["Making some plots."]];
q1=0;
q2=2*SLNMean[\[Mu],\[CapitalSigma]];

If[Verbose,Print["Number of fConv[_] stored: ",Length[DownValues[fConv]]]];

LegList = {"\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(FW\)]\)","\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(Sk\)]\)",
"\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(Cond\)]\)","\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(N\)]\)",
"\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(\[CapitalGamma]\)]\)","f"};

If[n<= 4,
	DensPlot = Plot[{fFW[x],fLSKN[x],fCondMC[x],fHermite[x],fLaguerre[x],fConv[x]},{x,0,q2},
		PlotPoints-> 20,MaxRecursion->2,ImageSize->Medium, 
		LabelStyle->{FontSize->13}, AspectRatio->0.3];
	
	ErrPlot = Plot[{fFW[x]-fConv[x],fLSKN[x]-fConv[x],fCondMC[x]-fConv[x],fHermite[x]-fConv[x],fLaguerre[x]-fConv[x]},{x,0,q2},
		PlotPoints-> 40,MaxRecursion->2,ImageSize->Medium, LabelStyle->{FontSize->13}, AspectRatio->0.3];

	Export[plotName, Legended[GraphicsColumn[{DensPlot, ErrPlot}],
		LineLegend[ColorData[97,"ColorList"], LegList]]];
	Print[plotName];

	If[Verbose,Print["Calculating the loss/error values for these estimators."]];

	res=L2Errors[fConv,{fFW,fLSKN,fCondMC,fHermite,fLaguerre},q1,q2/2]//AbsoluteTiming;
	Print[First[res]," seconds to evaluate L2 errors."];
	Print["L2 errors: {fFW, fLSKN, fCondMC, fHermite, fLaguerre} = ",Last[res]];
	Print["L2 errors (scaled): {fFW, fLSKN, fCondMC, fHermite, fLaguerre} = ",Last[res]/Min[Last[res]]];
	If[Verbose,Print["Number of fConv[_] stored: ",Length[DownValues[fConv]]]],

	(* Else n = 5, 6, ... *)
	Export[plotName,
		Plot[{fFW[x],fLSKN[x],fCondMC[x],fHermite[x],fLaguerre[x]},{x,0,q2},
		PlotLegends->LegList,PlotPoints-> 20,MaxRecursion->2,ImageSize->Medium, 
		LabelStyle->{FontSize->12}, AspectRatio->0.3,PlotRange->All]];
	Print[plotName]
];
];


AssessEstimatorsAgainstData[plotName_,R_:10^5,Ks_:{25,16},Verbose_: True]:=Module[
	{Dist,n,P,\[Rho],Norms,SLNs,QNorms,QSLNs,f,fFW,fLSKN,fCondMC,fCondMCQ,fHermite,fHermiteQ,
	fLaguerre,fKS,fLaguerreCMC,r1,r2,q1,q2,res,DensPlot,ErrPlot,LegList},

Dist=CopulaDistribution[{"Clayton", 0.1}, {LogNormalDistribution[0,1],LogNormalDistribution[0,1], LogNormalDistribution[0,1]}];
SLNs = Total[Transpose[RandomVariate[Dist, R]]];

f = GeneralConvolutionEstimator[Dist];
fHermite=HermiteEstimator[{},{},SLNs,Ks[[1]]];
If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(N\)]\)(1) = ",N[fHermite[1]]]];
fLaguerre=LaguerreEstimator[{},{},SLNs,Ks[[2]]];
If[Verbose,Print["\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(\[CapitalGamma]\)]\)(1) = ",N[fLaguerre[1]]]];

(*Make some plots.*)
If[Verbose,Print["Making some plots."]];
q1=0;
q2=2*Total[Mean[Dist]];

LegList = {"\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(N\)]\)",
"\!\(\*SubscriptBox[OverscriptBox[\(f\), \(^\)], \(\[CapitalGamma]\)]\)","f"};

	DensPlot = Plot[{fHermite[x],fLaguerre[x],f[x]},{x,0,q2},
		PlotPoints-> 20,MaxRecursion->2,ImageSize->Medium, 
		LabelStyle->{FontSize->13}, AspectRatio->0.3];
	

	If[Verbose,Print["Making error plot."]];
	ErrPlot = Plot[{fHermite[x]-f[x],fLaguerre[x]-f[x]},{x,0,q2},
		PlotPoints-> 20,MaxRecursion->2,ImageSize->Medium, LabelStyle->{FontSize->13}, AspectRatio->0.3];

	Export[plotName, Legended[GraphicsColumn[{DensPlot, ErrPlot}],
		LineLegend[ColorData[97,"ColorList"], LegList]]];
	Print[plotName];

	If[Verbose,Print["Calculating the loss/error values for these estimators."]];

	res=L2Errors[f,{fHermite,fLaguerre},q1,q2/2]//AbsoluteTiming;
	Print[First[res]," seconds to evaluate L2 errors."];
	Print["L2 errors: {fHermite, fLaguerre} = ",Last[res]];
	Print["L2 errors (scaled): {fHermite, fLaguerre} = ",Last[res]/Min[Last[res]]];
];
