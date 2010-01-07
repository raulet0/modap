# MODAP

class Fait(object):
    def __init__(self, fait):
        self.value = fait # instance de predicat (P a b)
        self.cycle = 0
        self.etat = "vivant"
    def __repr__(self):
        return "<%s %s %s>" % (self.__class__.__name__, self.value, self.etat)
    def set_value(self, fait): self.value = fait

class Regle(object):
    def __init__(self, conditions=[], actions=[]):
        self.cond1 = conditions
        self.condp = []
        self.condm = []
        self.act1 = actions
        self.actp = []
        self.actm = []
        self.vars = [] # liste des variables
        self.cpt = 0   # nombre de predicats positifs avec aucune instance dans BF
        self.spec = [] # liste des predicats negatifs en conclusion
        self.cycle = 0 # numero du dernier cycle ou la regle a ete saturee
        self.cout = 0

class Predicat(object):
    def __init__(self):
        self.filtres = [] # (* * non) 2 (f1 f2) (r1)

class Filtre(object):        
    def __init__(self):
        self.filtre = []
        self.nombre = 0
        self.faits = []
        self.regles = []

def ensemble1(liste):
    # Renvoie l'ensemble correspondant au multi-ensemble specifie.
    # Ex : (ensemble '(a () c () () c)) -> (a () c).
    if len(liste) == 0:
        return []
    elif liste[0] in liste[1:] :
        return ensemble1(liste[1:])
    else : 
        return [liste[0]] + ensemble1(liste[1:])
  
# print ensemble1([1,2,3,4,5,4,3,2,1])

fa1 = Fait(['homme','socrate'])
fa2 = Fait(['homme','rambo'])
re1 = Regle(conditions=[['homme','?x'],['adulte','?x']],
            actions=[['mortel','?x']])

