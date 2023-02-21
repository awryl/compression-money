import re
import sys

################## fonction utiles

def argmin (liste):
	i = 0
	i_min = 0
	v_min = liste[0]
	for x in liste:
		if (x < v_min):
			i_min = i
			v_min = x
		i = i+1
	return (i)

def signe (v,ref):
	if (ref >= 0):
		return v
	else:
		return -v

def noeud_max (_mat):
	n_max = 1
	for (a,b,v) in _mat:
		for x in a:
			if (x > n_max):
				n_max = x
		for y in b:
			if (x > n_max):
				n_max = x
	return n_max

def incidents (_mat,i):
	liste = []
	for (a,b,v) in _mat:
		if (i in a):
			for y in b:
				if (not(y in liste)):
					liste.append(y)
		if (i in b):
			for x in a:
				if (not(x in liste)):
					liste.append(x)
	return liste

################# fonctions de reduction, de compression et de decompression

# corrige la matrice si possible
def ini (_n,_mat):
	for (a,b,v) in _mat:
		for x in a:
			if (x <= 0 or x > _n):
				raise ValueError("Indice invalide", x)
		for y in b:
			if (y <= 0 or y > _n):
				raise ValueError("Indice invalide", y)
		a.sort()
		b.sort()
	return _mat

# supprime les 0
def clear (_mat):
	i = 0
	while (i < len(_mat)):
		(a,b,v) = _mat[i]
		if (v == 0.0):
			_mat.pop(i)
		else:
			i = i+1
	return _mat

# supprime toutes les occurences symetriques
def reduction_refl (_mat):
	i = 0
	while (i < len(_mat)):
		(a,b,v) = _mat[i]
		if (a == b):
			_mat.pop(i)
		else:
			i = i+1
	return _mat

def reduction_pos (_mat):
	i = 0
	for (a,b,v) in _mat:
		if (v < 0):
			_mat[i] = (b,a,-v)
		i = i+1
	return _mat

# regroupe toutes les dettes pour deux memes groupes
def reduction_sym (_mat):
	i = 0
	while (i < len(_mat)):
		(a,b,v) = _mat[i]
		for j in range(0,i):
			(a2,b2,v2) = _mat[j]
			if (a == a2 and b == b2):
				_mat[j] = (a2,b2,v2+v)
				_mat.pop(i)
				i = i-1
			elif (a == b2) and (b == a2):
				_mat[j] = (a2,b2,v2-v)
				_mat.pop(i)
				i = i-1
		i = i+1
	return _mat


# reduction destructive, simplifie les relations et elimine les boucles
def reduction_trans (_mat,bsym):
	fin = 0
	while (not fin):
		fin = 1
		i = 0
		while (i < len(_mat)):
			j = 0
			while (j < i):
				if (bsym):
					(a,b,v) = _mat[i]
					(a2,b2,v2) = _mat[j]
					if (a == a2 and b == b2):
						_mat[j] = (a2,b2,v2+v)
						_mat.pop(i)
						fin = 0
						i = i-1
					elif (a == b2) and (b == a2):
						_mat[j] = (a2,b2,v2-v)
						_mat.pop(i)
						fin = 0
						i = i-1	
				(a,b,v) = _mat[i]
				(a2,b2,v2) = _mat[j]			
				def resoudre_trans (g,c,d,vg,vd,posg,posd):
					v3 = signe(max(vg,vd)-min(vg,vd),max(vg,vd))
					v4 = min(abs(vg),abs(vd))
					if (vg*posg > 0):
						(a4,b4) = (d,g)
					else:
						(a4,b4) = (g,d)
					if (v4 == abs(vg)):
						if (posd > 0):
							(a3,b3) = (c,d)
						else:
							(a3,b3) = (d,c)
					else:
						if (posg > 0):
							(a3,b3) = (c,g)
						else:
							(a3,b3) = (g,c)				
					return (a3,b3,v3,a4,b4,v4)
				if (a == a2 and b != b2 and v*v2 < 0):
					(a3,b3,v3,a4,b4,v4) = resoudre_trans(b,a,b2,v,v2,1,1)
					fin = 0
				elif (a == b2 and b != a2 and v*v2 > 0):
					(a3,b3,v3,a4,b4,v4) = resoudre_trans(b,a,a2,v,v2,1,-1)
					fin = 0
				elif (b == a2 and a != b2 and v*v2 > 0):
					(a3,b3,v3,a4,b4,v4) = resoudre_trans(a,b,b2,v,v2,-1,1)
					fin = 0
				elif (b == b2 and a != a2 and v*v2 < 0):
					(a3,b3,v3,a4,b4,v4) = resoudre_trans(a,b,a2,v,v2,-1,-1)
					fin = 0
				else:
					(a3,b3,v3,a4,b4,v4) = (a,b,v,a2,b2,v2)
				_mat[i] = (a3,b3,v3)
				_mat[j] = (a4,b4,v4)
				j = j+1
				#print (_mat)
			i = i+1
	return _mat

def compression_groupe (liste,_mat):
	i = 0
	for (a,b,v) in _mat:
		if (all(x in liste for x in a) and all(y in liste for y in a)):
			_mat[i] = (liste,b,v)
		i = i+1
	return _mat


# le degre d'un noeud est le nombre d'aretes qui sont incidents au noeud
# le sous-degre d'un noeud relativement a un sous-graphe qui le contient est le degre du noeud dans le sous-graphe, le degre d'un graphe est le degre minimum des noeuds du graphe, le sous-degre d'un graphe relativement a un sous-graphe est le degre du sous-graphe
# deg_min=0:Id, deg_min=1:connexite, ..., deg_min=deg_max+1:partionnement complet
def compression_algo_sousdegre (_mat,deg_min):
	liste_incidences = []
	liste_deg = []
	for i in range(1,n_max+1):
		liste_incidences.append(incidents(_mat,i))
	fin = 0
	while (not fin):
		fin = 1
		for i in range(1,n_max+1):
			nouv_liste = []
			for j in liste_incidences[i]:
				if (len(liste_incidences[j]) >= deg_min):
					nouv_liste.append(j)
					fin = 0
			liste_incidences[i] = nouv_liste

		




	liste_fait = []
	_matc = []
	n_max = noeud_max(_mat)
	partition = [list(range(1,n_max+1))]
	for deg in range(1,deg_min):
		nouv_partition = []
		for part in partition:
			part2 = []
			if (deg == 1):
				0
			for (a,b,v) in _mat:
				0
			nouv_partition.append(part2)
		partition = sum(nouv_partition,[])
	return _mat 

# 0<densite:float<1
# le taux de densite d'un graphe est : d(G)=2a/(n(n-1)) (a:aretes,n:noeuds)
def compression_algo_densite (_mat,dens_min):
	return _mat

def compression (_mat):
	return compression_algo_soudegre (_mat,1)

def decompression (_mat):
	_mat2 = []
	for (a,b,v) in _mat:
		liste = []
		for x in a:
			liste2 = []
			v2 = v/len(a)
			for y in b:
				_mat2.append(([x],[y],v2/len(b)))
	return _mat2

def total (_mat,dec):
	if (dec):
		_mat = decompression(_mat)
	_mat = reduction_refl(_mat)
	_mat = reduction_pos(_mat)
	_mat = reduction_trans(_mat,1)
	return _mat



# lecture des fichiers, affectation des variables

def lecture_mat (_nom_fichier):
	fichier = open(_nom_fichier, 'r')
	i = 0
	_mat = []
	for line in fichier:
		line = re.sub(r'#.*\n','',line)
		if (line != ''):
			if (i == 0):
				_n = int(line)
			else:
				(aS,bS,vS) = line.split(':')
				a = [ int(x) for x in aS.split(',') ]
				b = [ int(x) for x in bS.split(',') ]
				v = float(vS)
				_mat.append((a,b,v))
			i = i+1
	fichier.close()
	return (_n,_mat)


# Types d'interaction pour acheter

def emission (a,b,v,_mat):
	return _mat.append((a,b,v))

def remboursement (a,b,v,_mat):
	return _mat

def reorientation (a,b,v,_mat):
	return _mat


# terminal pour log et ordres

nom_fichier = sys.argv[1] #"file.data"
(n,mat) = lecture_mat (nom_fichier)
#mat2 = mat[:]
print ('Matrice de depart :')
print (mat)
#mat = compression_groupe([1,2,3],mat)
#print(mat)
print ('Simplification totale...')
mat2 = total(mat,1)
print ('Matrice d\'arrivee :')
print (mat2)
print ()


# propriete des fonctions (R = R_trans) :
# 1) C.D.C = C
# 2) la somme des [liste] -> x (avec x dans [liste]) fait 0 dans la matrice compression_groupe(liste,mat), pour tout mat
# 3) R = R.D.C
# 4) D.C.D = D
