import sys

def char_range(a, b):
	res = []
	for i in range(ord(a), ord(b)+1):
		res.append(chr(i))
	return res

class SudokuSolver:
	def __init__(self, sudokuString): 
		self.domain = {}
		self.assignment = {}
		self.arcs = {}
		self.neighbors = {}
		self.initConstraints()
		self.initSudoku(sudokuString)

	def isSolved(self):
		for k, domain in self.domain.items():
			if self.assignment[k] == 0:
				return False
		return True

	def initConstraints(self):
		constraintMap = {}
		# alldiff rows, alldiff(a1, a2 ... a9) as binary arcs:
		# a1 != a2, a1 != a3 ..., a1 != a9; ... a9 != a1, a9 != a2 ... a9 != a8
		# ...
		# i1 != i2, i1 != i3 ..., i1 != i9; ... i9 != i1, i9 != i2 ... i9 != i8
		for i in char_range('a', 'i'):
			for j in range(1, 10):
				for k in range(1, 10):
					if k != j:
						if not i+str(j)+i+str(k) in constraintMap:
							self.appendArc(i+str(j), i+str(k))
							constraintMap[i+str(j)+i+str(k)] = 1

		# alldiff cols, alldiff(a1, b1 ... b9) as binary arcs:
		# a1 != b1, a1 != c1 ..., a1 != i1; ... i1 != a1, i1 != b1 ... i1 != h1
		# ...
		# a9 != b9, a9 != c9 ..., a9 != i9; ... i9 != a9, i9 != b9 ... i9 != h9
		for i in range(1, 10):
			for j in char_range('a', 'i'):
				for k in char_range('a', 'i'):
					if k != j:
						if not j+str(i)+k+str(i) in constraintMap:
							self.appendArc(j+str(i), k+str(i))
							constraintMap[j+str(i)+k+str(i)] = 1

		# alldiff blocks, alldiff(a1, b1, c1, a2, b2, c2, a3, b3, c3)
		# a1 != b1 ... a1 != c1; ... c1 != a1 ... c1 != b1
		# ...
		# a3 != b3 ... a3 != c3; ... c3 != a3 ... c3 != b2
		for colStride in range(3):
			for rowStride in range(3):
				for i in char_range(chr(ord('a')+rowStride*3), chr(ord('c')+rowStride*3)):
					for j in range(1+colStride*3, 4+colStride*3):
						lv = i + str(j)
						for k in char_range(chr(ord('a')+rowStride*3), chr(ord('c')+rowStride*3)):
							for l in range(1+colStride*3, 4+colStride*3):
								rv = k + str(l)
								if lv != rv:
									if not lv+rv in constraintMap:
										self.appendArc(lv, rv)
										constraintMap[lv+rv] = 1
	def appendArc(self, a, b):
		if not a in self.arcs:
			self.arcs[a] = []
		self.arcs[a].append(b)
		if not b in self.neighbors:
			self.neighbors[b] = []
		inNeighbors = False
		if not a in self.neighbors[b]:
			self.neighbors[b].append(a)

	def getArcs(self):
		arcs = []
		for a, bs in self.arcs.items():
			for b in bs:
				arcs.append([a, b])
		return arcs

	def getNeighbors(self, a, butC):
		neighbors = []
		if a in self.neighbors:
			for b in self.neighbors[a]:
				if b != butC:
					neighbors.append(b)
		return neighbors

	def initSudoku(self, sudokuString):
		strIndex = 0
		for i in char_range('a', 'i'):
			for j in range(1, 10):
				var = i + str(j)
				assignment = int(sudokuString[strIndex])
				domain = []
				if assignment == 0:
					for d in range(1, 10):
						domain.append(d)
				else:
					domain.append(assignment)
				self.assignment[var] = assignment
				self.domain[var] = domain
				strIndex += 1

	def getSudokuString(self):
		string = ""
		for i in char_range('a', 'i'):
			for j in range(1, 10):
				var = i + str(j)
				string = string + str(self.assignment[var])
		return string

	def ac3(self):
		queue = self.getArcs()
		infererredDomainReductions = []
		assignments = []
		while len(queue):
			arc = queue.pop(0)
			localInfererredDomainReductions = self.revise(arc[0], arc[1])
			infererredDomainReductions += localInfererredDomainReductions
			if len(localInfererredDomainReductions) > 0:
				if len(self.domain[arc[0]]) == 0:
					return [False, assignments, infererredDomainReductions]
				else:
					neighbors = self.getNeighbors(arc[0], arc[1])
					for k in neighbors:
						queue.append([k, arc[0]])

		for k, domain in self.domain.items():
			if self.assignment[k] == 0 and len(domain) == 1:
				self.assignment[k] = domain[0]
				assignments.append([k, domain[0]])
		
		return [True, assignments, infererredDomainReductions]

	def revise(self, i, j):
		excludedFromDomain = {}
		infererredDomainReductions = []
		for x in self.domain[i]:
			compatible = False
			for y in self.domain[j]:
				if x != y:
					compatible = True
			if not compatible:
				excludedFromDomain[x] = 1
				infererredDomainReductions.append([i, x])

		if len(excludedFromDomain) > 0:
			newDomain = []
			for x in self.domain[i]:
				if not x in excludedFromDomain:
					newDomain.append(x)
			self.domain[i] = newDomain
		return infererredDomainReductions

	def bts(self):
		if self.isSolved():
			return True
		var = self.selectUnassignedVariable()
		for value in self.domain[var]:
			assignments = [] # backtracking assignments info
			domainReductions = [] # backtracking domain substractions info
			if self.checkCompatibleAssignment(var, value):
				domainReductions += self.assignVarAndGetDomainReductions(var, value)
				assignments.append([var, value])
				inferences = self.ac3()
				assignments += inferences[1]
				domainReductions += inferences[2]
				if inferences[0] != False:
					if self.bts():
						return True
			# backtrack domain changes and assignments
			for assignment in assignments:
				self.assignment[assignment[0]] = 0
			for domainReduction in domainReductions:
				self.domain[domainReduction[0]].append(domainReduction[1])
		return False

	def selectUnassignedVariable(self):
		minVariable = 'a1'
		minDomain = 11
		for var, domain in self.domain.items():
			ld = len(domain)
			if ld > 1 and ld < minDomain:
				minVariable = var
				minDomain = ld
		return minVariable

	def checkCompatibleAssignment(self, var, value):
		affectedVars = self.arcs[var]
		for affectedVar in affectedVars:
			anyCompatibleAssignment = False
			for valueInDomain in self.domain[affectedVar]:
				if valueInDomain != value:
					anyCompatibleAssignment = True
					break
			if not anyCompatibleAssignment:
				return False
		# NOTE: Since sudoku has symmetrical arcs, neighbors are not checked, but we should
		return True

	def assignVarAndGetDomainReductions(self, var, value):
		domainReductions = []
		for valueInDomain in self.domain[var]:
			if valueInDomain != value:
				domainReductions.append([var, valueInDomain])
		self.domain[var] = [value]
		self.assignment[var] = value
		return domainReductions
		
	def dumpSudokuWithDomains(self):
		layout = []
		layout.append(list("  1   2   3    4   5   6    7   8   9   "))
		for i in char_range('a', 'i'):
			layoutI = 1+(ord(i)-ord('a'))*4
			layout.append(list( " +---+---+---++---+---+---||---+---+---+"))
			layout.append(list(i+"|   |   |   ||   |   |   ||   |   |   |"))
			layout.append(list( " |   |   |   ||   |   |   ||   |   |   |"))
			layout.append(list( " |   |   |   ||   |   |   ||   |   |   |"))
			for j in range(1, 10):
				layoutJ = 1+(j-1)*4+j//4+j//7+1-j//8
				v = i+str(j)
				domain = self.domain[v]
				k = len(domain)
				for l in range(0, k):
					layout[layoutI+1+l%3][layoutJ+l//3] = chr(ord('0')+domain[l])
		layout.append(list(" +---+---+---++---+---+---||---+---+---+"))
		for line in layout:
			print("".join(line))

def main():
	if len(sys.argv) != 2:
		print "Usage:",sys.argv[0],"<sudoku string>"
		print "  sudoku_string: for instance 094000130000000000000076002080010000032000000000200060000050400000008007006304008"
 		exit()

	inputSudokuString = sys.argv[1]

	sudokuSolver = SudokuSolver(inputSudokuString)
	sudokuSolver.ac3()

	if sudokuSolver.isSolved():
		print "Easy sudoku: solved just with constraint satisfaction"
		print sudokuSolver.dumpSudokuWithDomains()
	else:
		sudokuSolver.bts()
		print "Advanced sudoku: solved with constraint satisfaction + backtracking"
		print sudokuSolver.dumpSudokuWithDomains()

if __name__ == '__main__':
    main()
