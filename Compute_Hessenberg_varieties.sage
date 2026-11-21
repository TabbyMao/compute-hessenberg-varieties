Phi = RootSystem(['C',8])   # finite root system
I = Phi.index_set()   # for C3, (1,2,3)
C = matrix(ZZ,Phi.cartan_matrix()).transpose()   
# Cartan matrix <alpha_i,alpha_j> = (alpha_i,alpha_j^vee) 
# the defaut Cartan matrix seems to be (alpha_i^vee, alpha_j)
R = Phi.root_lattice()   # root lattice
Rc = Phi.coroot_lattice()   # coroot lattice
rank = Phi.cartan_type().rank()
simp   = R.simple_roots()   # simple roots
simpc  = Rc.simple_roots()   # simple coroots

def vec_in_standard_basis(x):   # Input: root/coroot; Output: coordinate under standard basis 
    V = x.parent().root_system.ambient_space()
    return V(x).to_vector()

def vec_in_simple_basis(x):   # Input: root/coroot; Output: coordinate under simple roots 
    v = vec_in_standard_basis(x)
    M = matrix([alpha.to_vector() 
                for alpha in Phi.ambient_space().simple_roots().values()]).transpose()
    return M.solve_right(v)


# simple roots, simple coroots -> coordinate under simple basis 
alpha      = {i: vec_in_simple_basis(simp[i])  for i in I}
alpha_vee  = {i: vec_in_simple_basis(simpc[i]) for i in I}
    
theta = R.highest_root()   # highest root vector
theta_vee = theta.associated_coroot()   # coroot of the highest root, distinguish from highest coroot

def pairing_root_coroot(a_vec, c_vec):   
    # inner-product in general
    # <·,·> = a^T*C*c (for ADE, i.e. c^v=c this equas pairing_root_root)
    # Input: coordinates under simple roots
    return QQ(a_vec * C * c_vec)

def pairing_root_root(a_vec,c_vec):
    # angle product <a,c> = (a,c^v) 
    # Input: root vectors a_vec, c_vec (in root lattice), e.g. simp[1], not coordinates
    a = vec_in_simple_basis(a_vec)   # to coordinate under simple basis
    cvee = c_vec.associated_coroot()   # alphacheck[]+alphacheck[]
    c = vector(QQ, [cvee.coefficient(i) for i in I])   # coeff under simple coroot basis
    return QQ(a * C * c)

def affine_simple_roots(root_system):   
    # define affine simple roots (finite_part_vector, level)
    # α_0 = δ - θ  stored as (-θ, 1), new direction δ
    # Output: ((),r), () coordinates of simple roots/-theta under simple basis
    I = root_system.index_set()
    root_lattice = root_system.root_lattice()
    simp = root_lattice.simple_roots()
    theta = root_lattice.highest_root()
    aff = {i: (vec_in_simple_basis(simp[i]), ZZ(0)) for i in I}
    aff[0] = (-vec_in_simple_basis(theta), ZZ(1))
    return aff

def affine_simple_coroots(root_system):   # define affine simple coroots, stored using coordinates under simple basis
    # α_0^∨ = K - θ^v stored as (-θ^v, 1)
    # central element K = 2δ/(θ,θ)
    I = root_system.index_set()
    simpc = root_system.coroot_lattice().simple_roots()
    affc = {i: (vec_in_simple_basis(simpc[i]), ZZ(0)) for i in I}
    affc[0] = (-vec_in_simple_basis(theta_vee), ZZ(1))
    return affc

# finite simple reflections on affine roots 
def s_finite_refl(i, x_n): 
    # Input: x_n=(x,n), x root vector; Output: Coordinate under simple basis 
    # s_i(x) = x - <x,alpha_i>alpha_i,  
    x, n = x_n
    k = pairing_root_root(x, simpc[i])
    return (vec_in_simple_basis(x) - k*alpha[i], n)

def s0_refl(x_n):   
    # s0(x+nδ)=(x-<x, θ>θ,(n+<x, θ>))
    x, n = x_n
    k = pairing_root_root(x, theta)   
    return (vec_in_simple_basis(x) - k*vec_in_simple_basis(theta), n+k)

def s_refl(i, x_n):
    # action of affine simple reflections
    # Input x_n=(x,n), x root vector; Output: ((coordinate under simple basis),k)
    return s0_refl(x_n) if i == 0 else s_finite_refl(i, x_n)

# Simple reflections on affine coroots 
def s_finite_on_coroot(i, c_m):
    # sα_i(c+mkappa)=c-<c,α_i>α_i+mkappa
    c, m = c_m
    k = pairing_root_root(c, simp[i])    
    return (vec_in_simple_basis(c) - k*alpha[i], m)

def s0_on_coroot(c_m):
    # check s0(c+mkappa)=c+(m-(c,theta))theta^vee+(c,theta)kappa
    c, m = c_m
    c = vec_in_simple_basis(c)
    k = pairing_root_coroot(c,vec_in_simple_basis(theta))       
    return (c + (m-k)*vec_in_simple_basis(theta_vee), k)

def s_on_coroot(i, c_m):
    return s0_on_coroot(c_m) if i == 0 else s_finite_on_coroot(i, c_m)


#############################################
# --- Action of a word in generators on affine (co)roots (left-to-right) ---
def act_word_on_alpha(word, a_n):
    x = a_n
    for i in word:
        x = s_refl(i, x)
    return x

def act_word_on_coroot(word, c_m):
    x = c_m
    for i in word:
        x = s_on_coroot(i, x)
    return x

# --- Optional: translations by λ ∈ Q^∨ ---
def t_lambda_on_alpha(lmbda_vec, a_n):
    a, n = a_n
    return (a, n - pairing_root_coroot(a, lmbda_vec))

def t_lambda_on_coroot(lmbda_vec, c_m):
    c, m = c_m
    return (c, m - pairing_root_coroot(lmbda_vec, c))




#####################################################
# Weight space decomposition of g((F))
positive_roots = R.positive_roots()
# rho = sum(positive_roots) / 2
Rcs = Phi.coroot_space()
rho_vee = sum((Rcs(alpha.associated_coroot()) for alpha in R.positive_roots()), Rcs.zero()) / 2

def grading_degree(alpha_r, nu):
    # Weight of x_alpha * t^r under the homogeneous grading 
    # (alpha+n*delta,nu*rho^vee+kappa)=nu(alpha,rho^vee)+r
    a,r = alpha_r
    return QQ(r) + QQ(nu) * vec_in_standard_basis(a) * vec_in_standard_basis(rho_vee)

#grading_degree((R.simple_roots()[1],0), 1/3)


def nu_alpha_rhov_values(nu_num, nu_den):
    # compute nu*(alpha,rho^vee) for each finite root alpha
    nu = QQ(nu_num) / QQ(nu_den)
    out = []
    for alpha in list(R.roots()):
        alpha_std = vec_in_standard_basis(alpha)
        val = nu * QQ(alpha_std * vec_in_standard_basis(rho_vee))
        out.append((alpha, alpha_std, val))
        #print("alpha =", alpha , alpha_std, "   nu*(alpha,rho^vee) =", val)
    return out

def group_roots_by_nu_alpha_rhov(nu_num, nu_den):
    # group finite roots by the same nu*(alpha, rho^vee)
    data = nu_alpha_rhov_values(nu_num, nu_den)
    groups = {}
    for alpha, alpha_std, val in data:
        groups.setdefault(val, []).append({
            "root": alpha,
            "standard_coords": alpha_std
        })

    return groups

def affine_roots_by_weights(nu_num, nu_den, targets):
    # for weight d/m, solve r + nu*(alpha,rho^vee) = d/m
    # so r = d/m - nu*(alpha,rho^vee)
    """targets: list of rational numbers, e.g. [QQ(0), QQ(1,3), QQ(2,3)]
    Return all pairs (alpha, r) such that
        r + nu*(alpha, rho^vee) = target
    with alpha shown in standard basis.
    """
    data = nu_alpha_rhov_values(nu_num, nu_den)
    out = {}

    for target in targets:
        target = QQ(target)
        out[target] = []

        for alpha, alpha_std, val in data:
            r = target - val
            if r in ZZ:
                out[target].append({
                    "root": alpha,
                    "standard_coords": alpha_std,
                    "r": ZZ(r)
                })

    return out


# Example: weights 0, 1/3, 2/3 for C3
weights = [QQ(k)/QQ(rank) for k in range(rank)]
pairs = affine_roots_by_weights(1, rank, weights)

for wt in weights:
    print("\n===================================")
    print("target weight =", wt)
    print("solutions of r + nu*(alpha,rho^vee) =", wt)
    print("===================================")
    for item in pairs[wt]:
#        print("alpha =", item["standard_coords"], "   r =", item["r"])
        print(
    " + ".join(
        [
            (f"e{i}" if c == 1 else f"-e{i}" if c == -1 else f"{c}e{i}")
            for i, c in enumerate(item["standard_coords"], start=1)
            if c != 0
        ]
        + [f"{item['r']}δ".replace("1δ", "δ").replace("-1δ", "-δ")] * (item["r"] != 0)
    ).replace("+ -", "- ")
)
        
        
        
########################################################################
########################################################################
n = rank
pairs = affine_roots_by_weights(1, n, [QQ(1)/QQ(n)])

# all indices for simple reflection e.g. [] for Id, [0], [1], [2,3]
words = [[]] + [[i] for i in range(n+1)] + [[i, i+1] for i in range(n)]

def W(word):   # rewrite [] for 1, [0,1] for s0s1
    return "1" if not word else "".join(f"s_{i}" for i in word)

def affine_root_from_simple_coords(x):
    # change coordinate under simple roots to root vector
    root = R.zero()
    for i in I:
        root += ZZ(x[i-1])*simp[i]
    return root

def refl(word, x_n):
     # Imput: x root vector; Output: (root vector,r)
     # Example: word=[0,1] computes s_0s_1(x), i.e. first s_1, then s_0 
    k = x_n
    for i in reversed(word):
        a,r = s_refl(i, k)
        k = (affine_root_from_simple_coords(a),r)
    return k
# usage s_refl(0,(-theta,1)), refl([0,1],(simp[1],1))


def is_positive_affine_root(x_n): #Input: x root vector
    x,r=x_n
    
    if r>0:
        return True
    if r<0: 
        return False
    return x in R.positive_roots()


# all affine roots in g(F)1/n, stored as (root vector,r)
roots = [
    (item["root"], item["r"])
    for item in pairs[QQ(1)/QQ(n)]
]


def L(a_r):   # used to print affine roots in g(F)1/n
    a, r = a_r   # Input: a, coordinate under simple basis e.g. L(((1,0,0),1))
    # change coordinate under simple basis into coordinate under standard basis
    M = matrix([a.to_vector() for a in Phi.ambient_space().simple_roots().values()]).transpose()
    v = M * vector(QQ, a) 
    terms = [
        (f"e{i}" if c == 1 else f"-e{i}" if c == -1 else f"{c}e{i}")
        for i, c in enumerate(v, 1) if c
    ]
    terms += [f"{r}δ".replace("1δ", "δ").replace("-1δ", "-δ")] * (r != 0)
    return " + ".join(terms).replace("+ -", "- ") or "0"


headers = ["w", "alpha"] + [L((vec_in_simple_basis(x[0]),x[1])) for x in roots]

rows = []
for word in words:
    alpha_col = "-" if not word else "(" + ", ".join(L(affine_simple_roots(Phi)[i]) for i in word) + ")"
    
    entries = []

    for x in roots:

        y_root = refl(list(reversed(word)), x)
       
        y_simple = (
            vec_in_simple_basis(y_root[0]),
            y_root[1]
        )

        if is_positive_affine_root(y_root):
            entries.append(L(y_simple))
        else:
            entries.append("[NEG] " + L(y_simple))

    rows.append([W(word), alpha_col] + entries)

widths = [
    max(len(str(row[j])) for row in [headers] + rows)
    for j in range(len(headers))
]

sep = "+".join("-" * (w + 2) for w in widths)

print(sep)

print("| " + " | ".join(
    str(headers[j]).ljust(widths[j])
    for j in range(len(headers))
) + " |")

print(sep)

for row in rows:

    print("| " + " | ".join(
        str(row[j]).ljust(widths[j])
        for j in range(len(row))
    ) + " |")

print(sep)