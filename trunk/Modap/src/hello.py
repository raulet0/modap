# MODAP v 1.0.0
#
# First lab model release (21/01/2010)
# First full functional release (07/03/2010)
#
###############################################################################

rulespath = '/workspace_python/Modap/src/'
trace = True
debug = False

###############################################################################
# Common tools

# >>> hello.hierarchical_list(['print','compteur:','[','?x','+',10,']'])
# ['print','compteur:',['?x','+',10]]
# >>> hello.hierarchical_list(['[','?x','+',10,']'])
#[['?x', '+', 10]]
# >>> hello.hierarchical_list(['print','[','?x','+',10,']','?y'])
# ['print', ['?x', '+', 10], '?y']
# >>> hello.hierarchical_list(['print','[','?x','*','[','?y','+',10,']',']','?z'])
# ['print', ['?x', '*', ['?y', '+', 10]], '?z']
def last_in_list(alist, aitem):
    ''' return index of last item in the list else return -1 if item not in list '''
    i = 0
    while aitem in alist[i:]: i = i + alist[i:].index(aitem) + 1
    return i - 1
def hierarchical_list(alist):
    if len(alist) == 0 or alist[0] == ']':
        return []
    elif alist[0] == '[':
        i = last_in_list(alist, ']')
        return [hierarchical_list(alist[1:i])] + hierarchical_list(alist[i+1:])
    else:
        return [alist[0]] + hierarchical_list(alist[1:])    

def ensemble1(liste):
    # not used in this release...
    # Renvoie l'ensemble correspondant au multi-ensemble specifie.
    # Ex : (ensemble '(a () c () () c)) -> (a () c).
    if len(liste) == 0:
        return []
    elif liste[0] in liste[1:] :
        return ensemble1(liste[1:])
    else : 
        return [liste[0]] + ensemble1(liste[1:])
  
# print ensemble1([1,2,3,4,5,4,3,2,1])

def permu(l, n):
    # print(l, n)
    if n == 0:
        return [[]]
    else:
        ret = []
        for x in l:
            lst = permu(l[l.index(x):][1:], n-1)
            res = map (lambda y: [x] + y, lst)
            ret = ret + res
        return ret

def parties(l, n):
    if n == 0:
        return []
    else:
        return permu(l, n) + (parties(l, n-1))

# >>> hello.parties(['a','b','c'],3) 
# [['a', 'b', 'c'], ['a', 'b'], ['a', 'c'], ['b', 'c'], ['a'], ['b'], ['c']]

def format_list(list):
    # return a formated list with parenthesis to print fact arguments
    if len(list) == 0: return ''
    s = str(list[0])
    for e in list[1:]:
        s = s + ',' + str(e)
    return s

###############################################################################

class Regle(object):
    def __init__(self, id): # BE CAREFUL with default values !
        self.nom = id   # rule name
        self.cond1 = [] # positives conditions
        self.condp = [] # functional programatic conditions
        self.condm = [] # negatives conditions
        self.act1 = []  # positives actions
        self.actp = []  # functional programatic actions
        self.actm = []  # negatives actions
        self.vars = []  # rule's variables list
        self.cpt = 0    # number of positive conditions with no instance in fact base
        self.spec = []  # list of negative predicates in action
        self.cycle = 0  # last cycle when rule fired
        self.cout = 0   # cost of firing this rule
    def __repr__(self):
        return "<%s %s:%s>" % (self.__class__.__name__, self.nom, self.cycle)

    def compteur(self, *valeur):
        if valeur:
            self.cpt = valeur[0] # first element of the tuple (n,)
        else:
            return self.cpt

    def affiche(self):
        print 'REGLE:', self.nom
        print ' cond+', self.cond1
        print ' condp', self.condp
        print ' condm', self.condm
        print ' act+ ', self.act1
        print ' actp ', self.actp
        print ' actm ', self.actm
        print " %s %s %s %s %s" % (self.vars,self.cpt,self.spec,self.cycle,self.cout)

###############################################################################

class Fait(object):
    def __init__(self, fait):
        self.value = fait # predicate instance (P a b)
        self.cycle = 0
        self.etat = 'mort'
    def __repr__(self):
        # return "<%s %s %s %s>" % (self.__class__.__name__, self.value, self.etat, self.cycle)
        return "%s(%s):%s:%s" % (self.value[0],format_list(self.value[1:]),self.etat[0],self.cycle)

    def setfait(self, etat): self.etat = etat
    
    def vivantq(self): return self.etat == 'vivant'

###############################################################################

class Predicat(object):
    def __init__(self, nom):
        self.id = nom
        self.filtres = {} # (* * non) 2 (f1 f2) (r1)
    def __repr__(self):
        return "<%s %s %s>" % (self.__class__.__name__, self.id, self.filtres)

###############################################################################

class Filtre(object):        
    def __init__(self, pattern, nb, liste_f, liste_r):
        self.filtre = pattern
        self.nombre = nb
        self.faits = liste_f
        self.regles = liste_r
    def __repr__(self):
        return "<%s %s %s %s %s>" % (self.__class__.__name__, self.filtre, self.nombre, self.faits, self.regles)

###############################################################################

class Moteur(object):
    def __init__(self):
        self.vide()

    def vide(self):
        self.regles = []  # rulebase, could be a dictionary
        self.dico = {}    # dictionary (hashtable), predicate is key
        self.faits = []   # factbase, could be a dictionary too...
        self.conflit = [] # conflict set
        self.cycle = 0    # rule engine cycle

    def videfaits(self):
        for fait in self.faits:
            self.retire(fait.value)
        self.faits = []
        
    def affdico(self):
        for token in self.dico.keys():
            print self.dico[token]
    def affregles(self):
        for rule in self.regles:
            rule.affiche()
    def affregle(self, rulename):
        for rule in self.regles:
            if rule.nom == rulename:
                rule.affiche()
    def afffaits(self):
        for fait in self.faits:
            print fait

    def basefaits(self):
        return filter(lambda fait: fait.vivantq(), self.faits)
    
    def instances(self, cond):
        # return filter(lambda fait: len(self.filtre(cond,fait.value(),{})) > 0, self.basefaits())
        stack = []
        for fait in self.faits:
            if fait.vivantq() and ( len(self.filtre(cond,fait.value,{}) ) > 0):
                stack.append(fait)
        return stack

    def lire(self,file):
        self.vide()
        filename = rulespath + file + '.reg.txt'
        print '-> opening', filename
        self.lireregles(filename)
        return self.regles

    def lireregles(self,fich):
        f = open(fich)
        self.premisse = False
        self.lp = [] # list of predicates
        for line in f:
            self.lireligne(line.split())
            if debug: print 'premisse',self.premisse
            if debug: print 'lp',self.lp
        f.close()

    def lireligne(self,ligne):
        # read a line in the rules file
        if debug: print ligne
        if len(ligne) == 0: return
        if ligne[0].upper() == 'REGLE':
            if len(self.regles) > 0: self.majcout(self.regles[-1]) # previous rule
            self.cregle(ligne[1]) # new rule
            self.lp = [] # RAZ for each rule
        elif ligne[0].upper() == '*':
            return
        elif ligne[0].upper() == 'SI':
            self.premisse = True
        elif ligne[0].upper() == 'ALORS':
            self.premisse = False
        elif ligne[0].upper() == 'FIN':
            self.majcout(self.regles[-1]) # last rule
        elif self.premisse:
            self.litp(ligne)
        else:
            self.lita(ligne)
            return

    def litp(self,ligne):
        if ligne[0] == 'absent':
            self.regles[-1].condm.append(ligne[1:])
        elif ligne[0][0] == '[': # functional condition
            self.regles[-1].condp.append(hierarchical_list(ligne[1:-1]))
        else:
            # create an instance of Predicate, add to dico
            # if necessary add a new instance of Filter to this predicate
            # deal with rule variables
            self.litpred(ligne)
            # append current rule to the rule list filter
            self.majreg1(self.dico[ligne[0]],self.cle(ligne[1:]))
            # refresh lp and rule 'compteur' attribute...
            forme = self.forme(ligne)
            if forme not in self.lp:
                self.lp.extend([forme,'+'])
                # TODO: use 'compteur' method instead
                self.regles[-1].cpt = self.regles[-1].cpt + 1
            # add this condition to the rule
            self.regles[-1].cond1.append(ligne)

    def lita(self,ligne):
        if ligne[0] == '+':
            # create an instance of Predicat, add to dico
            # if necessary add a new instance of Filter to this predicat
            hierarchical_line = hierarchical_list(ligne[1:])
            self.litact(hierarchical_line)
            self.regles[-1].act1.append(hierarchical_line)
        elif ligne[0] == '-':
            self.regles[-1].actm.append(hierarchical_list(ligne[1:]))
            self.majspem(ligne[1:])
        elif ligne[0][0] == '[':
            self.regles[-1].actp.append(hierarchical_list(ligne[1:-1]))

    def cregle(self, rulename): self.regles.append(Regle(rulename))
    
    def cpred(self, pred): # only name of predicat
        if pred not in self.dico.keys():
            self.dico[pred] = Predicat(pred)
        return self.dico[pred]
    
    def litpred(self, cond): # initial list form before creating a class instance
        pred, args = cond[0], cond[1:]
        predobj = self.cpred(pred)
        # if new, link a new instance of Filtre to the predicate instance
        self.majcle(predobj, self.cle(args))
        self.litvar(args)
        return predobj

    def litact(self, cond): # initial list form before creating a class instance
        pred, args = cond[0], cond[1:]
        predobj = self.cpred(pred)
        # if new, link a new instance of Filtre to the predicate instance
        self.majcle(predobj, self.cle(args))
        return predobj
    
    def litvar(self, args): return 0
    
    def majspem(self, conclusion):
        for i in range(0, len(self.lp), 2):
            if (self.lp[i][0] == conclusion[0]) and (self.lp[i+1] == '+'):
                if conclusion[0] not in self.regles[-1].spec:
                    self.regles[-1].spec.append(conclusion[0])                
                return 0

    def majcout(self, regle): return 0
    
    def majcle(self, pred, cle):
        if cle not in pred.filtres.keys():
            pred.filtres[cle] = Filtre(cle,0,[],[])

    def majreg1(self, pred, cle):
        # append current rule to the rule list filter
        if cle in pred.filtres.keys():
            if self.regles[-1] not in pred.filtres[cle].regles:
                pred.filtres[cle].regles.append(self.regles[-1])
                
    def forme(self, cond):
        pred, args = cond[0], cond[1:]
        return [pred] + map(lambda x: x, self.cle(args)) # tuple to list

    def construit1(self, regles):
        for r in regles:
            if r.compteur() > 0: r.compteur(r.compteur() - 1)

    def construitm(self, regles):
        for r in regles:
            r.compteur(r.compteur() + 1)
            if r in self.conflit: self.conflit.remove(r)

    def majec1(self, regles):
        for r in regles:
            if (r.compteur() == 0) and (not r in self.conflit):
                self.conflit = self.finsere(r, self.conflit)

    def finsere(self, regle, liste): # simplified release without rule cost sorting
        if len(liste) == 0:
            return [regle]
        else:
            return liste + [regle]

    def motcles(self, args):
        if len(args) == 0:
            return [()] # patterns are tuples
        else:
            l1 = map((lambda x: (args[0],) + x), self.motcles(args[1:]))
            l2 = map((lambda x: ('*',) + x), self.motcles(args[1:]))
            return l1 + l2

    def rfait(self, faitliste): # retrive a fact or return null
        for fact in self.faits:
            if faitliste == fact.value:
                return fact
        return None
    
    def ifait(self, faitliste): # retrieve an existing or create a new fact
        for fact in self.faits:
            if faitliste == fact.value:
                return fact
        newfact = Fait(faitliste)
        self.faits.append(newfact)
        return newfact

    def insere(self, faitliste): # BE CAREFUL : must not be a new instance of Fait !
        if faitliste[0] not in self.dico.keys(): return None # don't accept anything...
        fait = self.ifait(faitliste)
        if not fait.vivantq(): # is it a confirmation ?
            fait.setfait('vivant') # it is alive !
            fait.cycle = self.cycle # cycle where fact is alive
            # try to update all possible filters
            for motcle in self.motcles(fait.value[1:]): self.inseref(motcle, fait)
        return fait

    def inseref(self, motcle, fait):
        l1 = self.dico[fait.value[0]].filtres # dictionary of instances of filters
        if motcle in l1.keys():
            l2 = l1[motcle] # filter
            if l2.nombre == 0: self.construit1(l2.regles)
            self.majec1(l2.regles)
            l2.nombre = l2.nombre + 1
            l2.faits.append(fait)

    def retire(self, faitliste): # BE CAREFUL : must not be a new instance !
        if faitliste[0] not in self.dico.keys(): return None
        fait = self.rfait(faitliste)
        if fait == None: return None
        fait.setfait('mort')
        # try to update all possible filters
        for motcle in self.motcles(fait.value[1:]): self.retiref(motcle, fait)
        return fait

    def retiref(self, motcle, fait):
        l1 = self.dico[fait.value[0]].filtres # dictionary of instances of filters
        if motcle in l1.keys():
            l2 = l1[motcle] # filter
            if fait in l2.faits:
                if l2.nombre >= 1:
                    l2.nombre = l2.nombre - 1
                    if l2.nombre == 0: self.construitm(l2.regles)
                l2.faits.remove(fait)

    def variableq(self, arg): return isinstance(arg, str) and arg[0] == '?'

    def type(self, args, sub):
        # args is just the list of variables without predicate
        # sub is a list of variables with associated value (hashtable ?)
        return filter(lambda x: self.variableq(x) and not x in sub, args)
    
    def cyclef(self, fait): return fait.cycle
    
    def cycler(self, regle): return regle.cycle
    
    def nfaits(self, listef, regle):
        return filter(lambda fait: fait.cycle >= regle.cycle and fait.cycle < self.cycle, listef)
    
    def afaits(self, listef, regle):
        return filter(lambda fait: fait.cycle < regle.cycle, listef)

    def cle(self, args):
        result = ()
        for x in args:
            result = result + (('*',) if (isinstance(x, list) or self.variableq(x)) else (x,))
        return result

    def faits_premisse(self, condition, conditions, regle):
        cle = self.cle(condition[1:])
        fts = self.dico[condition[0]].filtres[cle].faits
        if condition in conditions:
            return self.nfaits(fts, regle)
        else:
            return self.afaits(fts, regle)

# hello.mot.faits_premisse(hello.mot.regles[0].cond1[0],[],hello.mot.regles[0])

    def verifp(self, l1, s1):
        for cond in l1:
            if eval(self.eval2str(self.subst(cond, s1))) == False:
                return False
        return True
 
    def verifm(self, l1, s1):
        for cond in l1:
            if len(self.instances(cond)) != 0: return False
        return True
 
    def choix(self, liste, subst, conditions, regle):
        # return [<first_condition>, <matchable_facts>, <conditions>, <current_rule>]
        return [liste[0], self.faits_premisse(liste[0], conditions, regle)]
   
    def possibles(self,l): return parties(l,len(l))
    
    def declenche(self, r1):
        if trace: print '-> declenche', r1
        if len(r1.cond1) > 1 and self.cycler(r1) > 0:
            possibles = self.possibles(r1.cond1)
        else:
            possibles = [r1.cond1]
        while r1 in self.conflit:
            self.cycle = self.cycle + 1
            self.conflit.remove(r1)
            for conditions in possibles:
                if debug: print '-> boucle-nouveaux-faits-pour',r1,conditions,'cycle',self.cycle
                self.saturer(r1.cond1, {}, 1, [], r1, conditions)
        r1.cycle = self.cycle
        return 0

    def saturer(self,l1,s1,k,p1,regle,conditions):
        if debug: print 2*k*' ','-> saturer',l1,s1,k,p1
        if len(l1) == 0:
            if self.verifp(regle.condp, s1) and self.verifm(regle.condm, s1):
                res = self.conclure(regle,s1,k,p1)
                return res
            else:
                return 0
        else:
            cond = self.choix(l1,s1,conditions,regle)
            res = self.matcher(cond[0],cond[1],k,l1,s1,p1,regle,conditions)
            if res != 0 and res == k:
                if debug: print 2*k*' ','=> saturer',l1,s1,k,p1
                res = self.saturer(l1,s1,k,p1,regle,conditions)
            if debug: print 2*k*' ','-> saturer',l1,s1,k,p1,'->', res
            return res
    
    def matcher(self,c1,lf,k,l1,s1,p1,regle,conditions):
        if debug: print 2*k*' ','-> matcher',c1,lf,k,l1,s1,p1
        if len(lf) == 0:
            # TODO: it could be noway !...
            if debug: print 2*k*' ','-> matcher',c1,lf,k,l1,s1,p1,'->', 0
            return 0
        else:
            # TODO: we have to be sure that lf[0] is always alive ?... 
            s2 = self.filtre(c1,lf[0].value,s1)
            if len(s2) != 0:
                res = self.saturer(l1[1:],s2[0],k+1,p1+[lf[0]],regle,conditions)
                if res != 0:
                    if debug: print 2*k*' ','-> matcher',c1,lf,k,l1,s1,p1,'->', res
                    return res
            res = self.matcher(c1,lf[1:],k,l1,s1,p1,regle,conditions)
            if debug: print 2*k*' ','-> matcher',c1,lf,k,l1,s1,p1,'->', res
            return res

    def filtre(self,e1,e2,env):
        sub = dict(env) # be careful with pointer to env !
        if len(e1) != len(e2): return []
        res = self.filtrex(e1,e2,sub)
        if debug: print '-> filtre',e1,e2,env,'->',res
        return res

# hello.mot.filtrex(['p','?x'],['p','a'],{})
# hello.mot.filtrex(['p','?x'],['p','a'],{'?x':'a'})
    
    def filtrex(self,e1,e2,env):
        if len(e1) == 0: # so len(e2) is expected to be the same
            return [env]
        elif e1[0] == e2[0]:
            return self.filtrex(e1[1:],e2[1:],env)
        else:
            return self.filtrer(e1[0],env[e1[0]] if e1[0] in env else None,e1,e2,env)
    
    def filtrer(self,p1,v1,e1,e2,env):
        if self.variableq(p1[0]): # p1[0] == '?'
            if len(p1) > 1:
                if v1 != None:
                    if v1 == e2[0]:
                        return self.filtrex(e1[1:],e2[1:],env)
                    else:
                        return []
                else:
                    env[e1[0]] = e2[0]
                    return self.filtrex(e1[1:],e2[1:],env)
            else:
                return self.filtrex(e1[1:],e2[1:],env)
        else:
            return []

    # def eval2str(self, alist): return str(eval(" ".join(alist)))

    def eval2str(self, alist):
        expr1 = "".join(alist)
        expr2 = str(eval(expr1))
        if debug: print 'EVAL:', expr1,'->', expr2
        return expr2

    def subst(self, cond, sub):
        if len(cond) == 0:
            return []
        elif isinstance(cond[0], list):
            return [self.eval2str(self.subst(cond[0], sub))] + self.subst(cond[1:], sub)
        elif self.variableq(cond[0]) and cond[0] in sub.keys():
            return [sub[cond[0]]] + self.subst(cond[1:], sub)
        else:
            return [cond[0]] + self.subst(cond[1:], sub)

    def conclure(self,regle,s1,k,p1):
        if debug: print 2*k*' ','-> conclure',regle,s1,k,p1
        self.conclurep(regle, s1, k, p1)
        self.conclure1(regle, s1, k, p1)
        return self.conclurem(regle, s1, k, p1)

    def conclurep(self,regle,s1,k,p1):
        for action in regle.actp:
            self.eval2str(self.subst(action, s1))
        return 0

    def conclurem(self,regle,s1,k,p1):
        # TODO: to be optimized
        ret = 999
        for action in regle.actm:
            fait = self.subst(action, s1)
            faitobj = self.retire(fait) # be careful, could be None
            if trace: print 3*k*' ','-> retire',faitobj
            if (action[0] in regle.spec):
                for i_fact in range(len(p1)):
                    if p1[i_fact].value == fait:
                        if i_fact + 1 < ret: ret = i_fact + 1
        if ret == 999:
            return 0
        else:
            return ret

    def conclure1(self,regle,s1,k,p1):
        for action in regle.act1:
            fait = self.subst(action, s1)
            faitobj = self.insere(fait)
            if trace: print 3*k*' ','-> ajoute',faitobj
        return 0

    def elire(self, ec): return ec[0] if len(ec) > 0 else None
    
    def infere(self):
        while len(self.conflit) > 0:
            self.declenche(self.elire(self.conflit))
        return self.basefaits()

###############################################################################
##
## Manual testing
##
###############################################################################

mot = Moteur()

def test0a():
    mot.insere(['fleur','vrai'])
    mot.insere(['graine'])
    mot.insere(['cotyledone','=','1'])
    mot.insere(['rhizome','faux'])
    # lilas
def test0b():
    mot.retire(['fleur','vrai'])
    mot.retire(['graine'])
    mot.retire(['cotyledone','=','1'])
    mot.retire(['rhizome','faux'])
def test2():
    mot.insere(['p','10','5'])
def test3():
    mot.insere(['tableau','t'])
    mot.insere(['t','1','2'])
    mot.insere(['t','2','3'])
    mot.insere(['t','3','4'])
    mot.insere(['t','4','5'])
    mot.insere(['t','5','1'])
def puzzle():
    # alain cueille gentiane
    # jean-marc cueille arnica
    # daniel cueille rhododindron
    # eric cueille chardon-bleu
    # patrick cueille edelweiss
    mot.insere(['card','alain','5'])
    mot.insere(['peutcueillir','alain','gentiane'])
    mot.insere(['peutcueillir','alain','arnica'])
    mot.insere(['peutcueillir','alain','rhododindron'])
    mot.insere(['peutcueillir','alain','edelweiss'])
    mot.insere(['peutcueillir','alain','chardon-bleu'])
    mot.insere(['card','eric','5'])
    mot.insere(['peutcueillir','eric','gentiane'])
    mot.insere(['peutcueillir','eric','arnica'])
    mot.insere(['peutcueillir','eric','rhododindron'])
    mot.insere(['peutcueillir','eric','edelweiss'])
    mot.insere(['peutcueillir','eric','chardon-bleu'])
    mot.insere(['card','patrick','5'])
    mot.insere(['peutcueillir','patrick','gentiane'])
    mot.insere(['peutcueillir','patrick','arnica'])
    mot.insere(['peutcueillir','patrick','rhododindron'])
    mot.insere(['peutcueillir','patrick','edelweiss'])
    mot.insere(['peutcueillir','patrick','chardon-bleu'])
    mot.insere(['card','daniel','5'])
    mot.insere(['peutcueillir','daniel','gentiane'])
    mot.insere(['peutcueillir','daniel','arnica'])
    mot.insere(['peutcueillir','daniel','rhododindron'])
    mot.insere(['peutcueillir','daniel','edelweiss'])
    mot.insere(['peutcueillir','daniel','chardon-bleu'])
    mot.insere(['card','jean-marc','5'])
    mot.insere(['peutcueillir','jean-marc','gentiane'])
    mot.insere(['peutcueillir','jean-marc','arnica'])
    mot.insere(['peutcueillir','jean-marc','rhododindron'])
    mot.insere(['peutcueillir','jean-marc','edelweiss'])
    mot.insere(['peutcueillir','jean-marc','chardon-bleu'])
    mot.insere(['cueille','alain','arnica','non'])
    mot.insere(['cueille','alain','rhododindron','non'])
    mot.insere(['cueille','alain','chardon-bleu','non'])
    mot.insere(['cueille','alain','edelweiss','non'])
    mot.insere(['cueille','jean-marc','edelweiss','non'])
    mot.insere(['cueille','jean-marc','rhododindron','non'])
    mot.insere(['cueille','jean-marc','chardon-bleu','non'])
    mot.insere(['cueille','eric','edelweiss','non'])
    mot.insere(['cueille','daniel','edelweiss','non'])
    mot.insere(['cueille','daniel','chardon-bleu','non'])

def action1(arg):
    ''' Sample action to be executed by rules '''
    print '###+> ACTION1',arg
def action2_affiche(arg1, arg2, arg3):
    ''' Sample action to be executed by rules '''
    print arg1, arg2, arg3
def condition1(arg1, arg2):
    ''' Sample condition to be directly tested by rules '''
    return (int(arg1) + int(arg2)) == 15

# hello.mot.lire('test0')
# hello.mot.affdico()
# hello.mot.affregles()
# hello.mot.affregle(<rulename>)
# hello.mot.afffaits()
# hello.mot.infere()
# hello.mot.videfaits()
# hello.mot.vide()
