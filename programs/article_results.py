"""The article's finite results, tables, and conventional mass coordinates.

The finite calculation is main_line_formulas.py. This program reads its computed
objects, prints them in article order, evaluates the three local characteristic
polynomials exactly, and carries the native quark roots with CRunDec. Comparison
records are read only after every finite quantity has been calculated.

Run from the repository root:
    python -I programs/article_results.py > outputs/article_results.out
"""
from contextlib import redirect_stdout
from fractions import Fraction
from itertools import permutations
from math import exp, log, pi, sqrt
from pathlib import Path
import io
import json
import runpy
import numpy as np
from scipy.integrate import quad
from scipy.special import zeta
import rundec

ROOT = Path(__file__).resolve().parents[1]
with redirect_stdout(io.StringIO()) as main_stdout:
    finite = runpy.run_path(str(ROOT / "programs" / "main_line_formulas.py"))
assert all(finite["ok"])
inputs = finite["INPUTS"]
rows = finite["ROWS"]
records = []
lines = []
checks = []


def scalar(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, (np.ndarray, list, tuple)):
        return [scalar(v) for v in value]
    if isinstance(value, (np.integer, int)):
        return int(value)
    if isinstance(value, (complex, np.complexfloating)):
        return {"real": float(value.real), "imaginary": float(value.imag)}
    if isinstance(value, (np.floating, float)):
        return float(value)
    return value


def shown(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, (float, np.floating)):
        return "%.15g" % value
    if isinstance(value, (int, np.integer)):
        return str(value)
    if isinstance(value, (np.ndarray, list, tuple)):
        return "[" + ", ".join(shown(v) for v in value) + "]"
    if isinstance(value, (complex, np.complexfloating)):
        return "%.15g%+.15gi" % (value.real, value.imag)
    return str(value)


def emit(key, quantity, value, unit="1", formula="", origin="finite comparison and step", article=None):
    line = "AR %s | %s = %s [%s]" % (key, quantity, shown(value), unit)
    if formula:
        line += " | " + formula
    lines.append(line)
    print(line)
    records.append(dict(id=key, quantity=quantity, value=scalar(value), unit=unit,
                        formula=formula, origin=origin, article=article,
                        program="programs/article_results.py",
                        output="outputs/article_results.out", line=len(lines)))


def check(key, condition, description):
    checks.append(bool(condition))
    emit("CHECK." + key, description, "ok" if condition else "FAIL", "check")
    if not condition:
        raise AssertionError(description)


# Polynomial coefficients are ordered by increasing power of u.
def add(a, b):
    out = [0] * max(len(a), len(b))
    for i, v in enumerate(a): out[i] += v
    for i, v in enumerate(b): out[i] += v
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i + j] += x * y
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out


def power(a, n):
    out = [1]
    for _ in range(n): out = mul(out, a)
    return out


def channel_det(grade):
    signs = [-1] * grade + [1] * (5 - grade)
    total = [0]
    for perm in permutations(range(5)):
        inv = sum(perm[i] > perm[j] for i in range(5) for j in range(i + 1, 5))
        term = [(-1) ** inv]
        for i, j in enumerate(perm):
            term = mul(term, [1] if i == j else [0, -signs[i]])
        total = add(total, term)
    return total


check("main_line", len(finite["ok"]) == 29 and all(finite["ok"]), "main-line checks 29/29")
local = {n: channel_det(n) for n in (0, 2, 4)}
for n in (0, 2, 4):
    lhs = mul([1, 0, -1], local[n])
    rhs = mul(mul(power([1, 1], 5 - n), power([1, -1], n)), [1, -(5 - 2 * n), 4])
    check("encounter.N%d" % n, lhs == rhs,
          "(1-u^2) det(I-u E_%d(J-I))=(1+u)^%d(1-u)^%d k_%d(u)" % (n, 5 - n, n, n))
    emit("eq:encounter_first.N%d" % n, "det(I-u B_S) coefficients", local[n],
         "integer polynomial", article="eq:encounter_first")
product = mul(mul(local[0], power(local[2], 10)), power(local[4], 5))
bass = mul(power([1, 0, -1], 24), mul([1, -5, 4], mul(power([1, -1, 4], 10), power([1, 3, 4], 5))))
check("encounter.product", product == bass and len(product) == 81,
      "sixteen channel determinants give the degree-80 Bass polynomial")
emit("eq:polynomial.coefficients", "D(u) coefficients", product, "integer polynomial", article="eq:polynomial")


# The invariant pairing gives the matrix transpose on the other component.
J_pair = 2 * finite["Om"].reshape(4, 4)
probe_X = np.arange(16).reshape(4, 4)/7 + 1j*np.arange(16)[::-1].reshape(4, 4)/11
X_sharp = J_pair @ probe_X.T @ np.linalg.inv(J_pair)
check("crossing", np.allclose(np.kron(np.eye(4),probe_X)@finite["Om"], np.kron(X_sharp,np.eye(4))@finite["Om"]),
      "(I tensor X) Omega=(J X^T J^-1 tensor I) Omega for the printed matrix representation")

# Use the oriented gamma basis of the article for the north-pole curvature.
gamma = [g.copy() for g in finite["gam"]]
gamma_product = gamma[0]@gamma[1]@gamma[2]@gamma[3]@gamma[4]
if np.allclose(gamma_product,-np.eye(4)):
    gamma[4] *= -1
P_plus=(np.eye(4)+gamma[4])/2
curvature={(a,b):P_plus@gamma[a]@gamma[b]@P_plus/2 for a in range(4) for b in range(4) if a!=b}
def epsilon4(p):
    return (-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
asd=True
for a in range(4):
    for b in range(a+1,4):
        dual=sum(epsilon4((a,b,c,d))*curvature[c,d]/2 for c in range(4) for d in range(4) if len({a,b,c,d})==4)
        asd &= np.allclose(dual,-curvature[a,b])
density=sum(epsilon4(p)*np.trace(curvature[p[0],p[1]]@curvature[p[2],p[3]])/4 for p in permutations(range(4)))
check("instanton",asd and abs(density-3)<1e-12,"north-pole curvature is anti-self-dual and tr(F wedge F)=3 vol")
emit("ap:unit-instanton.density","tr(F wedge F) density",float(density.real),"unit S4 volume", "(1/8pi^2)*3*(8pi^2/3)=1",article="ap:unit-instanton")

# The [3,2] character is the two-subset permutation character minus the
# one-subset permutation character. Evaluate the central projector on all S5.
perms=list(permutations(range(5)))
weights={}
for p in perms:
    fixed=sum(p[i]==i for i in range(5))
    fixed_pairs=sum({p[i],p[j]}=={i,j} for i in range(5) for j in range(i+1,5))
    parity=(-1)**sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))
    weights[p]=1+parity+5*(fixed_pairs-fixed)
projector=True
for g in perms:
    convolution=0
    for h in perms:
        inv=tuple(h.index(i) for i in range(5))
        convolution += weights[h]*weights[tuple(inv[g[i]] for i in range(5))]
    projector &= convolution==120*weights[g]
k_values=[Fraction(weights[p],120) for p in ((0,1,2,3,4),(1,0,2,3,4),(1,2,0,3,4))]
check("mixing.idempotent",projector and k_values==[Fraction(9,40),Fraction(1,24),Fraction(-1,40)],
      "S5 central kernel is a convolution idempotent; k(1),k((ab)),k((abc))=9/40,1/24,-1/40")

# Positive source weights, summed through k=200. Their tail is geometric.
q_source=finite["af"]**finite["n_pos"]
probability=[exp(-q_source*log(4))]
for k in range(200):
    probability.append(probability[-1]*(3/4)*(q_source+k)/(k+1))
mean_source=sum(k*p for k,p in enumerate(probability))
second_source=sum(k*k*p for k,p in enumerate(probability))
check("source.positive",all(p>0 for p in probability) and abs(sum(probability)-1)<1e-14
      and abs(mean_source/(3*q_source)-1)<1e-13 and abs((second_source-mean_source**2)/(12*q_source)-1)<1e-13,
      "positive stationary weights normalize and have mean 3a^11 and variance 12a^11")
emit("ap:positive-stationary-source.moments","sum p_k,mean,variance",[sum(probability),mean_source,second_source-mean_source**2],
     formula="p_0=4^-q; p_(k+1)=(3/4)(q+k)/(k+1)p_k; q=a^11",article="ap:positive-stationary-source")

# Numerical details in the article's order. All aliases refer to the objects
# computed above from the 16 comparison states and 80 directed states.
f = finite
alpha, alphas = f["alpha"], f["alphas"]
sos, shat = f["osw"], f["sw"]
alpha2 = alpha / ((1 - f["ff"]) * sos)
alphaY = alpha2 * sos / (1 - sos)
g2sq, g1sq = 4 * pi * alpha2, 4 * pi * alphaY
mp_GeV = f["mp"] / 1000
MR = f["mpl"] * float(Fraction(1, 3) ** 9)
Rc = f["af"] ** 16 * MR / mp_GeV
As = 12 * f["af"] ** 11 * (inputs["primordial_pivot_Mpc_inv"] * f["ellR"]) ** (-1 / 40)
Xn = 1 - 2 * f["bf"]
MH = (f["mp"] + f["me"]) / 1000 - inputs["hydrogen_binding_eV"] * 1e-9
kappa_analytic = (1 - 2 * Xn) * MH / mp_GeV + Xn / 2 * inputs["helium_atom_mass_GeV"] / mp_GeV
kappa_network = inputs["network_baryon_mass_factor"]
nu = f["neut"]
V, U = f["Vq"], f["Ul"]

numeric = [
("eq:four-five", "dim_C H, dim_R Q", [finite["gam"][0].shape[0],len(finite["gam"])], "1", "2 quaternionic components; five traceless real components"),
("eq:spectrum", "L eigenvalues with multiplicity", f["specL"], "1", "L=I+sum gamma_t tensor gamma_t"),
("eq:B", "comparison states, directed states, transitions", [16, int(f["B"].shape[0]), int(f["B"].sum())], "1", "B(x',s;x,t)=[s!=t][x'=x xor g_s]"),
("eq:division_values", "chi at 1/4,i/4,-1/4,-i/4", [0, -5-3j, -10, -5+3j], "1", "chi=1/u+4u-5"),
("eq:signed_first_return", "Phi(1), Phi(i)", [Fraction(-1,19), Fraction(-1,13)], "1", "Phi(z)=-z^4/(16+3z^2)"),
("eq:grade_amplitudes", "t_0,r_0,t_v,r_v", [Fraction(2,5),Fraction(3,5),Fraction(2,3),Fraction(1,3)], "1", "ratios of k_N(-1/4)"),
("eq:return_numbers", "F(1), E N_ret, a", [1,16,Fraction(5,38)], "1", "F(1)=1; F'(1)=16; a=(1-Phi(1))/8"),
("eq:stationary.counts", "M,C_h,C_j", [f["M"],f["Ch"],f["Cj"]], "1", "directed transitions retained through grade four"),
("eq:stationary.ratios", "c_L,sigma,eta_0,R_ud", [Fraction(15,74),Fraction(75,74),Fraction(295,296),Fraction(17,37)], "1", "ratios of retained counts"),
("eq:green", "b", Fraction(7,16), "1", "(F-0)^T(5I-A)^+(F-0)"),
("eq:electric_small", "f,nu", [Fraction(9,250),Fraction(9,4000)], "1", "r_0^2/10; f/E N_ret"),
("eq:hnu", "h_nu", f["hov"], "1", "[M_Q(nu)M_Q(-nu)]^(-3/2)"),
("eq:Nh", "N_h", f["Nh"], "1", "sum j=1..59; absolute tail < 1e-143"),
("eq:alpha", "alpha^-1", 1/alpha, "1", "[1-nu h_nu/(297+N_h)]/(c_L f)"),
("eq:strong", "alpha_s", alphas, "1", "||r_v I_8/8||_F"),
("eq:electron_mark", "d arg(4u_c)/d theta at zero", Fraction(1,320), "1", "one marked transition in B"),
("eq:Rp", "R_p", f["rp"], "1", "1836+log(5/2)/6-a^5-b a^6"),
("eq:Rn", "R_n", f["rn"], "1", "t_0^[-(5a^4+4a^10+10 c_L b a^6)]"),
("eq:family_source", "r_mu,r_tau,p_q,q_q,kappa_u", [f["rmu"],f["rtau"],f["pq_p"],f["pq_q"],f["kap_u"]], "1", "L(10,2,+),L(5,-2,+),L(10,2,-),L(5,-2,-),(3/2)^(8/5)"),
("eq:leptons", "m_e,m_mu,m_tau", [f["me"],f["me"]*f["rmu"],f["me"]*f["rmu"]*f["rtau"]], "MeV", "m_e (1,r_mu,r_mu r_tau)"),
("eq:quarks.down", "m_d,m_s,m_b native", f["down"], "MeV", "3^(3/2)m_e(1/eta_0,p_q/eta_0,p_q q_q)"),
("eq:quarks.up", "m_u,m_c,m_t native", f["up"], "MeV", "R_ud(m_d,kappa_u^5 m_s,kappa_u^(15/2)m_b)"),
("eq:quark_invariant", "m_b^2 m_d/m_s^3", rows["B06"], "1", "q_q^2 eta_0^2/p_q"),
("eq:fermi.W", "W_W", f["WW"], "1", "F(h_nu) h_nu^-4 (1-2b+2b h_nu)"),
("eq:fermi.GF", "G_F", f["GF"], "GeV^-2", "9 W_W/(10 M^2 m_p^2)"),
("eq:fermi.v", "v", f["v"], "GeV", "(sqrt(2)G_F)^(-1/2)"),
("eq:weak_angles", "s_hat^2,s_OS^2,s_eff^2", [shat,sos,3*f["Ncon"]], "1", "3N_h,3N_h/(1+f),3N_con"),
("eq:weak_coefficients", "g_2^2,g_1^2,alpha_2,alpha_Y", [g2sq,g1sq,alpha2,alphaY], "1", "g_2^2=4 pi alpha/[(1-f)s_OS^2]; g_1^2=g_2^2 s_OS^2/(1-s_OS^2)"),
("eq:weak_masses", "M_W,M_Z", [f["mw"],f["mz"]], "GeV", "v sqrt(pi alpha/[(1-f)s_OS^2]); M_W/sqrt(1-s_OS^2)"),
("eq:higgs_top.coefficients", "lambda_H,chi_h,y_t^2", [f["lamH"],Fraction(30,169),Fraction(59,60)], "1", "pi alpha/chi_h; eta_0/sigma"),
("eq:higgs_top.masses", "m_H,m_t radial", [f["mh"],f["mt"]], "GeV", "v sqrt(2lambda_H); v sqrt(eta_0/(2sigma))"),
("eq:W", "W", f["W"], "1", "(2/5)^48 (295/296)^9"),
("eq:EH", "Lambda ell^2", 3, "1", "oriented spinor curvature trace"),
("eq:planck.strength", "G m_p^2/(hbar c)", f["W"]**2, "1", "W^2"),
("eq:planck.mass", "M_Pl", f["mpl"], "GeV", "m_p/W"),
("eq:planck.length", "ell_P", f["W"]*f["lp"]*1e-15, "m", "W hbar/(m_p c)"),
("eq:neutral_scales", "V_R,M_R", [Fraction(1,3)**9,MR], "1,GeV", "det_R(G^-1 H)=3^-9; M_Pl V_R"),
("eq:neutrino_matrix.rho", "rho_nu", f["rho"], "1", "tan(pi/8)^2"),
("eq:neutrino_matrix.Dirac", "Dirac singular values d_i", f["sigf"]*f["v"]*np.array([0,sqrt(f["rho"]),1])/sqrt(2), "GeV", "sigma v (0,sqrt(rho_nu),1)/sqrt(2)"),
("eq:neutrino_roots", "light neutrino masses", nu*1000, "meV", "2d_i^2/[M_R+sqrt(M_R^2+4d_i^2)]"),
("eq:quark_angles", "s12,s23,s13,delta_q", [f["s12"],f["s23"],f["s13"],f["dq"]], "1,1,1,rad", "9/40,1/24,3/800,arg(7+16i)"),
("eq:mixing_idempotent", "k(identity),k(transposition),k(three-cycle)", k_values, "1", "[1+sgn(g)+5 chi_[3,2](g)]/120"),
("eq:whole_phase", "theta_c,s_F", [f["tau_"],Fraction(3,50)], "1", "2pi/(16R_p); r_0/10"),
("eq:Lambda.curvature", "Lambda ell_P^2", f["lam"], "1", "3 W^6 theta_c s_F^3"),
("eq:Lambda.length", "ell", f["ellR"], "Mpc", "lambda_p/[W^2 sqrt(theta_c s_F^3)]"),
("eq:population_source", "E K,Var K,positive comparison states", [3,12,f["n_pos"]], "1", "G_K(x)=1/(4-3x); rank Pi_(L>0)"),
("eq:primordial.eta", "eta_B", 3*f["af"]**11, "1", "C'(0)=3a^11"),
("eq:primordial.source", "C''(0)", 12*f["af"]**11, "1", "12a^11"),
("eq:primordial.As", "A_s,ln(10^10 A_s)", [As,log(1e10*As)], "1", "12a^11(k_* ell)^(-1/40)"),
("eq:primordial.tilt", "n_s,dn_s/dlogk", [Fraction(39,40),0], "1", "1-t_0/E N_ret; constant power"),
("eq:Neff", "N_eff", rows["F04"], "1", "3 eta_0 sigma^(4/3)"),
("eq:cold.Rc", "R_c", Rc, "1", "a^16 M_R/m_p"),
("eq:epoch", "rho_Lambda/rho_m,Omega_m/(1-Omega_r),Omega_Lambda/(1-Omega_r)", [Fraction(24,11),Fraction(11,35),Fraction(24,35)], "1", "Tr L^2/4=24; positive comparison rank=11"),
]
for key, name, value, unit, formula in numeric:
    # A suffix distinguishes several independently printed quantities of one display.
    label = ":".join(key.split(":")[:2]).split(".")[0]
    emit(key, name, value, unit, formula, article=label)
check("mixing.unitarity", np.allclose(V.conj().T@V,np.eye(3)) and np.allclose(U.conj().T@U,np.eye(3)), "V and U are unitary")
check("neutrino.poles", np.allclose(nu*1e-9*(MR+nu*1e-9),(f["sigf"]*f["v"]*np.array([0,sqrt(f["rho"]),1])/sqrt(2))**2), "three light zeros satisfy m_i(M_R+m_i)=d_i^2")
emit("COMPOSITION.Xn", "analytic neutron fraction", Xn, formula="1-2b")
emit("COMPOSITION.kappa.analytic", "analytic kappa_B", kappa_analytic, formula="(1-2X_n)M_H/m_p+(X_n/2)M_He/m_p", origin="finite X_n and atomic-composition inputs")
emit("COMPOSITION.ratio.analytic", "analytic Omega_c/Omega_b", Rc/kappa_analytic, formula="R_c/kappa_B analytic", origin="finite cold ratio and atomic composition")
emit("COMPOSITION.kappa.network", "network kappa_B", kappa_network, formula="rho_b/(m_p n_b c^2)", origin="recorded nucleosynthesis-network composition input")
emit("COMPOSITION.ratio.network", "network Omega_c/Omega_b", Rc/kappa_network, formula="R_c/kappa_B network", origin="finite cold ratio and recorded network composition")

# CRunDec 3.1 through the rundec 0.7 Python binding. Masses are in GeV.
# Starting coordinates: native roots identified with MSbar masses at the
# computed M_Z, alpha_s(M_Z)=1/sqrt(72). The matching scale is m_b(m_b).
rd = rundec.CRunDec()
native = {"u": f["up"][0]/1000, "d": f["down"][0]/1000,
          "s": f["down"][1]/1000, "c": f["up"][1]/1000,
          "b": f["down"][2]/1000, "t": f["up"][2]/1000}
mb = rd.mMS2mSI(native["b"], alphas, f["mz"], 5, 4)
ab5 = rd.AlphasExact(alphas, f["mz"], mb, 5, 4)
ab4 = rd.DecAsDownSI(ab5, mb, mb, 4, 4)
a2 = rd.AlphasExact(ab4, mb, inputs["light_quark_reporting_scale_GeV"], 4, 4)
qcd = {"b":mb}
for name in ("u","d","s","c"):
    at_bottom = rd.mMS2mMS(native[name], alphas, ab5, 5, 4)
    below_bottom = rd.DecMqDownSI(at_bottom, ab5, mb, mb, 4, 4)
    qcd[name] = (rd.mMS2mSI(below_bottom, ab4, mb, 4, 4) if name=="c"
                 else rd.mMS2mMS(below_bottom, ab4, a2, 4, 4))
for order in range(1,5):
    self_mass = rd.mMS2mSI(native["t"], alphas, f["mz"], 5, order)
    alpha_top = rd.AlphasExact(alphas, f["mz"], self_mass, 5, order)
    pole_mass = rd.mMS2mOS(self_mass, None, alpha_top, self_mass, 6, order)
    emit("QCD.top.%d" % order, "m_t(m_t),alpha_s(m_t),M_t", [self_mass,alpha_top,pole_mass], "GeV,1,GeV", "n_f=5 running; five massless light flavours in pole conversion", origin="CRunDec; %d loops" % order)
qcd["t"] = pole_mass
emit("QCD.thresholds", "m_b(m_b),alpha_s^(5)(m_b),alpha_s^(4)(m_b),alpha_s^(4)(2GeV)", [mb,ab5,ab4,a2], "GeV,1,1,1", "4-loop running and bottom matching", origin="CRunDec")
for name in ("u","d","s","c","b","t"):
    emit("QCD."+name, "transported "+name+" mass", qcd[name]*(1000 if name in ("u","d","s") else 1), "MeV" if name in ("u","d","s") else "GeV", "2 GeV" if name in ("u","d","s") else ("pole" if name=="t" else "mbar(mbar)"), origin="CRunDec explicit prescription")

# The exact integral convention of the Supplemental Material, with a=alpha_s/(4pi).
aQ = alphas/(4*pi)
beta0,beta1,beta2,beta3 = 23/3,116/3,9769/54,-598391/1458+(352864/81)*zeta(3,1)
def remainder(x):
    return (beta0*beta2-beta1**2+(beta0*beta3-beta1*beta2)*x-beta1*beta3*x*x)/(beta0**2*(beta0+beta1*x+beta2*x*x+beta3*x**3))
integral, quadrature_error = quad(remainder,0,aQ,epsabs=1e-15,epsrel=1e-13)
log_scale = 1/(beta0*aQ)+beta1/beta0**2*log(beta0*aQ)+integral
emit("QCD.Lambda.integral", "finite beta integral,log(mu^2/Lambda^2)", [integral,log_scale], formula="four-loop beta polynomial, n_f=5", origin="beta function integral")
for label, scale in (("S14",f["mz"]),("S017",inputs["Z_reporting_scale_1_GeV"]),("S018",inputs["Z_reporting_scale_2_GeV"])):
    emit("QCD."+label, "Lambda_5", scale*1000*exp(-log_scale/2), "MeV", "mu=%.15g GeV"%scale, origin="four-loop beta function integral")

# The article's values and measurements are comparison records. They enter
# here, after the finite and transported quantities have been calculated.
reference = json.loads((ROOT/"data"/"article_table_records.json").read_text())
carried = json.loads((ROOT/"data"/"conventional_records.json").read_text())
T1_values = [f["W"]**2,f["mpl"],3,f["lam"],alphas,0,1/alpha,alpha2,alphaY,f["GF"],f["v"],shat,sos,3*f["Ncon"],f["ff"],f["mw"],f["mz"],f["mw"]/f["mz"],f["lamH"],f["mh"],Fraction(59,60),f["mt"],f["rp"],f["rn"],f["me"],MR,3*f["af"]**11,As,Fraction(39,40),rows["F04"],Rc,Rc/kappa_network,0,Fraction(24,11)]
T1_units = ["1","GeV","1","1","1","1","1","1","1","GeV^-2","GeV","1","1","1","1","GeV","GeV","1","1","GeV","1","GeV","1","1","MeV","GeV","1","1","1","1","1","1","1","1"]
for entry,value,unit in zip(reference["table_1"],T1_values,T1_units):
    origin = "measured mass unit" if entry["id"]=="T1.25" else ("finite R_c divided by recorded network composition" if entry["id"]=="T1.32" else "finite comparison and step")
    relation=entry["relation"]
    deviation=None
    if "measurement" in entry:
        measurement=entry["measurement"]
        comparison_value=log(1e10*As) if entry["id"]=="T1.28" else float(value)
        difference=comparison_value-measurement["central"]
        deviation=difference/measurement["upper_sigma" if difference>=0 else "lower_sigma"]
        relation += "; deviation = %+.6g sigma" % deviation
    emit(entry["id"],entry["quantity"],value,unit,relation,origin,article=entry["id"])
    records[-1]["computed_deviation"] = deviation
    records[-1]["measurement"] = entry.get("measurement")
    records[-1]["article_value"] = entry["calculated"]
    records[-1]["comparison"] = entry["comparison"]
    records[-1]["article_deviation"] = entry["deviation"]
emit("T1.28.log", "ln(10^10 A_s)", log(1e10*As), article="T1.28")

T2 = {
"T2.F1.nu":(nu[0],"meV"),"T2.F1.e":(f["me"],"MeV"),
"T2.F1.u.native":(f["up"][0],"MeV"),"T2.F1.d.native":(f["down"][0],"MeV"),
"T2.F2.nu.mass":(nu[1]*1000,"meV"),"T2.F2.nu.split":(nu[1]**2,"eV^2"),
"T2.F2.mu.mass":(f["me"]*f["rmu"],"MeV"),"T2.F2.mu.ratio":(f["rmu"],"1"),
"T2.F2.c.native":(f["up"][1],"MeV"),"T2.F2.s.native":(f["down"][1],"MeV"),
"T2.F3.nu.mass":(nu[2]*1000,"meV"),"T2.F3.nu.split":(nu[2]**2,"eV^2"),
"T2.F3.tau.mass":(f["me"]*f["rmu"]*f["rtau"],"MeV"),"T2.F3.tau.ratio":(f["rtau"],"1"),
"T2.F3.t.native":(f["up"][2]/1000,"GeV"),"T2.F3.b.native":(f["down"][2],"MeV"),
"T2.CKM.s12":(f["s12"],"1"),"T2.CKM.s23":(f["s23"],"1"),"T2.CKM.s13":(f["s13"],"1"),"T2.CKM.delta":(f["dq"],"rad"),"T2.CKM.J":(rows["C05"],"1"),
"T2.PMNS.s12":(f["S12"],"1"),"T2.PMNS.s13":(f["S13"],"1"),"T2.PMNS.s23":(f["S23"],"1"),"T2.PMNS.delta":(rows["C14"],"degree"),"T2.PMNS.J":(f["jl"],"1")}
for name,matrix in (("V",V),("U",U)):
    for i in range(3):
        for j in range(3): T2["T2.%s%d%d"%(name,i+1,j+1)] = (abs(matrix[i,j]),"1")
coordinate_rows = {"T2.F1.u.carried":("u","I01"),"T2.F1.d.carried":("d","I02"),"T2.F2.s.carried":("s","I03"),"T2.F2.c.carried":("c","I04"),"T2.F3.b.carried":("b","I05"),"T2.F3.t.carried":("t","I07")}
for entry in reference["table_2"]:
    key=entry["id"]
    if key in coordinate_rows:
        name,rid=coordinate_rows[key]
        unit="MeV" if name in ("u","d","s") else "GeV"
        value=qcd[name]*(1000 if unit=="MeV" else 1)
        emit(key,entry["quantity"],value,unit,"explicit four-loop mass prescription","CRunDec",article=key)
        records[-1]["article_value"] = entry["calculated"]
        records[-1]["record_id"] = rid
        emit(key+".article",entry["quantity"]+" article record",carried[rid]["value"],unit,origin="conventional calculation record of the article",article=key)
        emit(key+".difference","explicit calculation minus article record",value-carried[rid]["value"],unit,origin="difference of the two preceding results",article=key)
    else:
        value,unit=T2[key]
        emit(key,entry["quantity"],value,unit,origin="mass unit" if key=="T2.F1.e" else "finite comparison and step",article=key)
        records[-1]["article_value"] = entry["calculated"]
check("article.tables", set(r["id"] for r in records) >= set(e["id"] for e in reference["table_1"]+reference["table_2"]), "84 main-table addresses printed")

for key,quantity,value,unit,formula in (
    ("K04","m_beta,m_betabeta",[sqrt(sum(abs(U[0])**2*nu**2)),abs(sum(U[0]**2*nu))],"eV","sqrt(sum |U_ei|^2 m_i^2), |sum U_ei^2 m_i|"),
    ("T05","m_1,m_2",nu[:2],"eV","the first two light rest roots"),
    ("L02","tau-current probabilities",abs(U[2])**2,"1","|U_tau,i|^2")):
    emit("CATALOGUE."+key,quantity,value,unit,formula)
z_first=Fraction(1,4)**59
bound_coefficient=(1+z_first)/(16-8*z_first-3*z_first**2-3*z_first**3)
tail_bound=bound_coefficient*z_first**4/(1-Fraction(1,4)**4)
check("return.tail",float(tail_bound)<1e-143 and 0<f["hov"]<=1,"absolute repeated-return tail after j=59 is below 1e-143")
emit("RETURN.tail_bound","absolute tail bound",float(tail_bound),formula="[(1+r)/(16-8r-3r^2-3r^3)] r^4/(1-4^-4), r=4^-59")

# Every formula printed by the main-line program retains its own address. The
# numerical rows printed beside it are read from that calculation's ROWS object.
formula_lines = []
for line in f["MD"]:
    if line.startswith("**("):
        number=int(line.split(")",1)[0][3:])
        formula_lines.append((number,line.split("**",2)[2].strip()))
for number,formula in formula_lines:
    selected = {rid:scalar(value) for rid,value in rows.items() if f["TAG"].get(rid)=="(%d)"%number}
    emit("MF.%02d"%number,"main-line formula",formula,"formula")
    records[-1]["computed_rows"] = selected
    if selected:
        emit("MF.%02d.rows"%number,"computed numerical rows", "; ".join(rid+"="+shown(value) for rid,value in selected.items()),"table units")

# The full Supplemental catalogue uses the same finite calculations. The
# second evaluator also supplies its three list-valued rows and light-pair
# return function, which is used here for the displayed composite expressions.
with redirect_stdout(io.StringIO()):
    catalogue_calculation=runpy.run_path(str(ROOT/"programs"/"table_from_the_step.py"))
assert all(catalogue_calculation["ok"])
catalogue=dict(catalogue_calculation["R"])
light=catalogue_calculation["level"]
pair=lambda x,y: f["mp"]*sqrt(6*catalogue_calculation["response"]([x,y]))
s_r=catalogue["J07"]*1e6
literal={
    "J10":sqrt((pair(light["u"],light["u"])**2+pair(light["d"],light["d"])**2)/2),
    "J11":pair(light["d"],light["d"]),"J12":pair(light["s"],light["s"]),
    "J19":sqrt(s_r),"J20":sqrt(s_r+catalogue["J09"]**2),"J21":sqrt(s_r+catalogue["J08"]**2),
    "J22":sqrt(s_r+pair(light["s"],light["s"])**2),
    "J26":f["mn"]*f["K0f"]**(f["Cj"]/int(f["B"].sum())),
    "J28":f["mn"]*f["K0f"]**(2*f["Cj"]/int(f["B"].sum())),
    "J30":3*f["bf"]*f["mp"]*f["K0f"]**(20/int(f["B"].sum())),
    "J31":3*f["bf"]*f["mp"]*f["K0f"]**(40/int(f["B"].sum())),
    "J32":3*f["bf"]*f["mp"]*f["K0f"]**(60/int(f["B"].sum()))}
catalogue.update(literal)
emit("COMPOSITE.light_levels","S_u,S_d,S_s",[light[k] for k in ("u","d","s")],formula="pion source with pair overlap c=8/15")
emit("COMPOSITE.upper_bound","upper bound of the positive two-mode branch",f["mp"]*sqrt(12*log(4/3)),"MeV","m_p sqrt(12 log(4/3))")
primitive={
 "P01":[f["LOm"],2,-2],"P02":[f["kept"],f["moved"]],"P03":-1,
 "P04":[sum(f["Y"]),sum(y**3 for y in f["Y"])],"P05":[f["gev"][-3]/f["gev"][-1],1-f["gev"][-3]/f["gev"][-1]],
 "P06":[int(sum(f["sig"]<0)),int(sum(f["sig"]>0))],"P07":[int(f["B"].shape[0]),int(f["B"].sum())],
 "P08":f["kN"](0,Fraction(1,4)),"P09":[f["chi"](u) for u in (0.25,0.25j,-0.25,-0.25j)],
 "P10":[f["K"][n] for n in (0,2,4)]+[f["t_"],f["e_"],f["tl_"],f["el_"]],
 "P11":f["m2c"],"P12":"cos(omega)=cos(mu)cos(k)","P13":[Fraction(1,200),Fraction(1,98)],
 "P14":3*f["El"],"P15":3,"P16":1,"P17":[f["El"],f["Varl"]],"P18":[Fraction(-1,19),Fraction(-1,13)],
 "P19":[f["EnF"],f["EnL"],f["VarnF"],f["VarnL"],f["Cov"],f["xc"],f["EKf"],f["VarKf"]],
 "P20":[f["M"],f["Ch"],f["Cj"]],"P21":Fraction(7,16),
 "P22":[Fraction(5,38),Fraction(13,12),Fraction(3,13),Fraction(30,169)],
 "P23":[Fraction(1,72),Fraction(1,18),Fraction(1,12)],"P24":f["LOm"]*f["M"]+f["Ch"],
 "P25":Fraction(1,int(f["B"].sum())),"P26":[Fraction(9,250),Fraction(9,4000)],
 "P27":f["hov"],"P28":f["Nh"],"P29":f["x_"],"P30":f["WW"],"P31":f["W"]**2,
 "P32":[Fraction(1,28),Fraction(-1,22),Fraction(-1,6),Fraction(1,2)],
 "P33":[f["VarD"],f["exc_mean"]],"P34":f["detF0"],"P35":f["contr"],"P36":f["axial"],"P37":rows["K01"]}
supplemental=json.loads((ROOT/"data"/"supplemental_records.json").read_text())
for record in supplemental:
    rid=record["id"]
    if rid in primitive:
        value,origin=primitive[rid],"finite structural calculation; general statement in the cited proof"
    elif rid in catalogue:
        value = catalogue[rid]
        if rid in literal:
            origin = "literal composite expression"
        elif rid in ("A002", "A003"):
            origin = "finite mass with the stated 5/36 pion ansatz"
        elif rid in ("H01", "H02", "L18", "L08", "C16", "L06", "F13", "L07", "D07", "L09"):
            origin = "stated continuum equation evaluated with finite coefficients"
        elif rid == "S05":
            origin = "finite axial and mixing coefficients with the declared neutron-rate normalization"
        else:
            origin = "finite numerical catalogue"
    elif rid=="F02":
        value,origin=Rc/kappa_network,"finite cold reading divided by declared network composition"
    elif rid in ("S14","S017","S018"):
        scale={"S14":f["mz"],"S017":inputs["Z_reporting_scale_1_GeV"],"S018":inputs["Z_reporting_scale_2_GeV"]}[rid]
        value,origin=scale*1000*exp(-log_scale/2),"evaluated four-loop beta-function integral"
    elif rid=="L21":
        endpoint_dirac=f["sigf"]*f["v"]*sqrt(f["WW"])*np.array([0,sqrt(f["rho"]),1])/sqrt(2)
        endpoint_light=2*endpoint_dirac**2/(MR+np.sqrt(MR**2+4*endpoint_dirac**2))*1e9
        value,origin=float(sum(endpoint_light)),"light roots evaluated at the clock endpoint h_nu=1"
    elif rid in carried:
        value,origin=carried[rid]["value"],"declared conventional calculation record"
    else:
        value,origin=record.get("value","analytic expression"),"analytic comparison record"
    relation = record.get("formula", "") + "; operation: " + origin
    deviation = None
    measurement = record.get("measurement")
    if measurement and isinstance(value, (int, float, np.integer, np.floating, Fraction)):
        difference = float(value) - measurement["central"]
        width = measurement["upper_sigma" if difference >= 0 else "lower_sigma"]
        if width > 0:
            deviation = difference / width
            relation += "; deviation = %+.6g sigma" % deviation
    emit("SI."+rid, record["quantity"], value, record["unit"], relation, origin)
    records[-1].update(reference_value=record.get("value"), comparison=record.get("comparison"),
                      recorded_deviation=record.get("residual"), computed_deviation=deviation,
                      measurement=measurement, theorems=record.get("theorems", []), supplemental_id=rid)
check("supplemental",len(supplemental)==252 and len({r["id"] for r in supplemental})==252,"252 Supplemental records printed with their calculated or declared origin")

check("formulas",len(formula_lines)==73,"73 main-line formulas printed")
emit("SUMMARY","checks passed,total checks,table addresses,main-line formulas",[sum(checks),len(checks),84,73],"count")
(ROOT/"outputs"/"article_results.json").write_text(json.dumps(records,indent=2,ensure_ascii=False)+"\n")
