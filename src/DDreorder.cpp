/*
 * This file is part of IIC-JKU DD package which is released under the MIT license.
 * See file README.md or go to http://iic.jku.at/eda/research/quantum_dd/ for more information.
 */

#include "DDpackage.h"
#include <ctime>

namespace dd {

	void Package::recomputeMatrixProperties(Edge in) {
		if (isTerminal(in))
			return;

		if (in.p->computeMatrixProperties == Recompute) {
			for (const auto & e : in.p->e)
				recomputeMatrixProperties(e);

			in.p->computeMatrixProperties = computeMatrixProperties;
			checkSpecialMatrices(in.p);
		}
	}

	void Package::markForMatrixPropertyRecomputation(Edge in) {
		if (isTerminal(in))
			return;

		if (in.p->computeMatrixProperties != Recompute) {
			for (const auto & e : in.p->e)
				markForMatrixPropertyRecomputation(e);

			in.p->computeMatrixProperties = Recompute;
		}
	}

	void Package::resetNormalizationFactor(Edge in, Complex defaultValue) {
		if (isTerminal(in))
			return;

		if (in.p->normalizationFactor == defaultValue)
			return;

		for (const auto & e : in.p->e)
			resetNormalizationFactor(e, defaultValue);

		if (defaultValue == CN::ZERO && in.p->normalizationFactor != CN::ONE)
			unnormalizedNodes--;

		in.p->normalizationFactor = defaultValue;
	}

	Edge Package::renormalize(Edge in) {
		const auto before = cn.cacheCount;

		in = renormalize2(in);
		resetNormalizationFactor(in, CN::ZERO);
		resetNormalizationFactor(in, CN::ONE);

		const auto after = cn.cacheCount;
		assert(before == after);

		return in;
	}

	Edge Package::renormalize2(Edge in) {
		if (isTerminal(in))
			return in;

		nOps[CTkind::renormalize]++;

		auto weight = in.w;
		in.w = CN::ONE;

		auto r = CTlookup(in, in, CTkind::renormalize);

		if (r.p!= nullptr) {
			if (r.w != CN::ZERO) {
				auto c = cn.getTempCachedComplex();
				CN::mul(c, r.w, weight);
				r.w = cn.lookup(c);
				if (CN::equalsZero(r.w)) {
					return DDzero;
				}
			}
			return r;
		}

		std::array<Edge, NEDGE> e{};
		for (int i=0; i<NEDGE; ++i) {
			e[i] = renormalize2(in.p->e[i]);
		}

		if (in.p->normalizationFactor != CN::ONE) {
			auto factor = in.p->normalizationFactor;
			in.p->normalizationFactor = CN::ONE;
			r = makeNonterminal(in.p->v, e);
			in.p->normalizationFactor = factor;
			auto c = cn.getTempCachedComplex();
			CN::mul(c, r.w, factor);
			r.w = cn.lookup(c);
		} else {
			r = makeNonterminal(in.p->v, e);
		}

		CTinsert(in, in, r, CTkind::renormalize);

		auto c = cn.getTempCachedComplex();
		CN::mul(c, r.w, weight);
		r.w = cn.lookup(c);

		return r;
	}

	void Package::reuseNonterminal(short v, const Edge *edge, NodePtr p) {
		Edge e{p, CN::ONE};
		e.p->computeMatrixProperties = computeMatrixProperties;
		e.p->v = v;
		std::memcpy(e.p->e, edge, NEDGE * sizeof(Edge));
		auto olde = e;
		Node old{};
		memcpy(&old, e.p, sizeof(Node));
		e = normalize(e, false);
		if (olde.p != e.p) {
			std::cerr << "something went wrong during normalization in reuseNonterminal" << std::endl;
		}

		if (e.w != CN::ONE) {
			if (e.p->normalizationFactor == CN::ONE) {
				unnormalizedNodes++;
				e.p->normalizationFactor = e.w;
			} else {
				auto c = cn.getTempCachedComplex();
				CN::mul(c, e.p->normalizationFactor, e.w);
				e.p->normalizationFactor = cn.lookup(c);
			}
			e.w = CN::ONE;

			if (e.p->normalizationFactor == CN::ONE)
				unnormalizedNodes--;
		}
		// !problematic if lookup would change NodePtr
		olde = e;
		e = UTlookup(e);
		assert(olde.p == e.p);
	}

	void Package::exchange(unsigned short i, unsigned short j) {
		if (i == j) {
			return;
		} else if (i > j) {
			return exchange(j, i);
		}

		if ((i + 1) == j)
			return exchangeBaseCase(j);

		auto g = static_cast<short>(i + 1);

		// shuffeling the lower level i up until it is in its position
		while (g < j)
			exchangeBaseCase(g++);
		exchangeBaseCase(g);

		// shuffeling the upper level j down until it is in its position
		while (g > i+1)
			exchangeBaseCase(--g);
	}

	void Package::exchangeBaseCase(unsigned short i) {
		// copy unique table from higher variable and empty it
		std::array<NodePtr, NBUCKET> table{};
		for (unsigned short t=0; t<NBUCKET; ++t) {
			table[t] = Unique[i][t];
			Unique[i][t] = nullptr;
		}

		// iterate over all obtained nodes
		for (unsigned short t=0; t<NBUCKET; ++t) {
			NodePtr p = table[t];
			while (p != nullptr) {
				NodePtr pnext = p->next;
				if (p->ref != 0) {
					exchangeBaseCase2(p, i);
				}
				p = pnext;
			}
		}
	}

	void Package::exchangeBaseCase2(NodePtr p, unsigned short i) {
		Edge t[NEDGE][NEDGE]{ }, newEdges[NEDGE]{ };

		// creating matrix T
		for (int x = 0; x < NEDGE; x++) {
			for (int y = 0; y < NEDGE; y++) {
				if (p->e[y].p->v == i-1) {
					t[x][y] = p->e[y].p->e[x];
					auto c = cn.getTempCachedComplex();
					CN::mul(c, p->e[y].p->e[x].w, p->e[y].w);
					if (p->e[y].p->normalizationFactor != CN::ONE) {
						CN::mul(c, c, p->e[y].p->normalizationFactor);
					}
					t[x][y].w = cn.lookup(c);
				} else {
					// edge pointing to a terminal or skipped variable
					t[x][y] = p->e[y];
				}
			}
		}

		// creating new nodes and appending corresponding edges
		for (int x = 0; x < NEDGE; ++x) {
			newEdges[x] = makeNonterminal(static_cast<short>(i-1), t[x]);
			incRef(newEdges[x]);
		}
		for (auto& x : p->e)
			decRef(x);

		// reuse p to build new top node
		reuseNonterminal(static_cast<short>(i), newEdges, p);
	}

	/// Dynamically reorder a given decision diagram with the current variable map using the specific strategy
	/// \param in decision diagram to reorder
	/// \param varMap stores the variable mapping. varMap[circuit qubit] = corresponding DD qubit, e.g.
	///			given the varMap (reversed var. order):
	/// 			0->2,
	/// 			1->1,
	/// 			2->0
	/// 		the circuit operation "H q[0]" leads to the DD equivalent to "H q[varMap[0]]" = "H q[2]".
	///			the qubits in the decision diagram are always ordered as n-1 > n-2 > ... > 1 > 0
	/// \param strat strategy to apply
	/// \return the resulting decision diagram (and the changed variable map and output permutation, which are returned as reference)
	Edge Package::dynamicReorder(Edge in, std::map<unsigned short, unsigned short>& varMap, DynamicReorderingStrategy strat) {
		switch (strat) {
			case None: return in;
			case Sifting: return sifting(in, varMap);
			case Random: return random(in, varMap);
			case Window2: return window2(in, varMap);
			case Window3: return window3(in, varMap);
			case Window4: return window4(in, varMap);
		}

		return in;
	}

	/// Apply sifting dynamic reordering to a decision diagram given the
	/// current variable map \param in decision diagram to apply sifting to
	/// \param varMap stores the variable mapping (cf. dynamicReorder(...))
	/// \return the resulting decision diagram (and the changed varMap, which is returned as reference)
	Edge Package::sifting(Edge in, std::map<unsigned short, unsigned short>& varMap) {
		const auto n = static_cast<short>(in.p->v + 1);
		std::vector<bool> free(n, true);
		std::map<unsigned short, unsigned short> invVarMap{};
		for (const auto & i : varMap)
			invVarMap[i.second] = i.first;

		computeMatrixProperties = Disabled;
		Edge root{in};

		short pos = -1, optimalPos, originalPos;
		int max;
		unsigned long min;
		for (int i = 0; i < n; ++i) {

			min = activeNodeCount;
			max = 0;
			for (short j = 0; j < n; j++) {
				if (free[varMap[j]] && active[varMap[j]] > max) {
					max = active[varMap[j]];
					pos = j;
				}
			}
			free[varMap[pos]] = false;
			optimalPos = pos;
			originalPos = pos;

			if (pos < n / 2) {  // variable is in lower half -> sifting to bottom first
				// sifting to bottom
				while (pos > 0) {
					exchangeBaseCase(pos);
					--pos;
					if (activeNodeCount < min) {
						min = activeNodeCount;
						optimalPos = pos;
					}
				}

				// sifting to top
				while (pos < n - 1) {
					exchangeBaseCase(pos + 1);
					++pos;
					if (activeNodeCount < min) {
						min = activeNodeCount;
						optimalPos = pos;
					}
				}

				// sifting to optimal position
				while (pos > optimalPos) {
					exchangeBaseCase(pos);
					--pos;
				}
			} else {  // variable is in upper half -> sifting to top first
				// sifting to top
				while (pos < n - 1) {
					exchangeBaseCase(pos + 1);
					++pos;
					if (activeNodeCount < min) {
						min = activeNodeCount;
						optimalPos = pos;
					}
				}

				// sifting to bottom
				while (pos > 0) {
					exchangeBaseCase(pos);
					--pos;
					if (activeNodeCount < min) {
						min = activeNodeCount;
						optimalPos = pos;
					}
				}

				// sifting to optimal position
				while (pos < optimalPos) {
					exchangeBaseCase(pos + 1);
					++pos;
				}
			}

			// there are nodes which need to renormalized
			if (unnormalizedNodes > 0) {
				auto oldroot = root;
				root = renormalize(root);
				incRef(root);
				decRef(oldroot);
				in.p = root.p;
				in.w = root.w;
				if (unnormalizedNodes > 0) {
					std::cerr << "Renormalization failed. " << unnormalizedNodes << " nodes remaining." << std::endl;
				}
			}
			computeMatrixProperties = Enabled;
			markForMatrixPropertyRecomputation(root);
			recomputeMatrixProperties(root);

			// Adjusting varMap if position changed
			if (optimalPos > originalPos) {
				auto tempVar = invVarMap[originalPos];
				for (int j = originalPos; j < optimalPos; ++j) {
					invVarMap[j] = invVarMap[j + 1];
					varMap[invVarMap[j]] = j;
				}
				invVarMap[optimalPos] = tempVar;
				varMap[invVarMap[optimalPos]] = optimalPos;
			} else if (optimalPos < originalPos) {
				auto tempVar = invVarMap[originalPos];
				for (int j = originalPos; j > optimalPos; --j) {
					invVarMap[j] = invVarMap[j - 1];
					varMap[invVarMap[j]] = j;
				}
				invVarMap[optimalPos] = tempVar;
				varMap[invVarMap[optimalPos]] = optimalPos;
			}
		}

		return in;
	}

	/// First counts the number of nodes in the given DD.
	/// Then a loop is executed nodeCount-many times and inside
	/// this loop two randomly selcted levels are swap.
	/// \param in decision diagram to operate on
	/// \param varMap stores the variable mapping (cf. dynamicReorder(...))
	/// \return the resulting decision diagram (and the changed varMap, which is returned as reference)
	Edge Package::random(Edge in, std::map<unsigned short, unsigned short>& varMap) {
		int n = (in.p->v + 1);
		unsigned long min = activeNodeCount;
		std::queue<Edge> q{ };
		int nodeCount = 0;
		std::srand(std::time(nullptr));
		Edge root{in};

		computeMatrixProperties = Disabled;
		visited.clear();
		q.push(in);
		while (!q.empty()) {
			Edge e = q.front();
			if (visited.insert(e.p).second) ++nodeCount;
			q.pop();

			for (auto& x : e.p->e)
				if (x.p != nullptr && !isTerminal(x)) q.push(x);
		}

		for (int x = 0; x < nodeCount; x++) {
			int i = std::rand() % n;
			int j = std::rand() % n;

			exchange(varMap[i], varMap[j]);

			if (min > activeNodeCount) {
				min = activeNodeCount;

				unsigned short temp = varMap[i];
				varMap[i] = varMap[j];
				varMap[j] = temp;
			} else {
				exchange(varMap[j], varMap[i]);
			}

			// there are nodes which need to renormalized
			if (unnormalizedNodes > 0) {
				auto oldroot = root;
				root = renormalize(root);
				incRef(root);
				decRef(oldroot);
				in.p = root.p;
				in.w = root.w;
				if (unnormalizedNodes > 0) {
					std::cerr << "Renormalization failed. " << unnormalizedNodes << " nodes remaining." << std::endl;
				}
			}
			computeMatrixProperties = Enabled;
			markForMatrixPropertyRecomputation(root);
			recomputeMatrixProperties(root);
		}

		return in;
	}

	/// Tries all permutations in a window of size 2.
	/// Permutation with lowest node count is choosen.
	/// Shifts this window from the bottom to the top.
	/// \param in decision diagram to operate on
	/// \param varMap stores the variable mapping (cf. dynamicReorder(...))
	/// \return the resulting decision diagram (and the changed varMap, which is returned as reference)
	Edge Package::window2(Edge in,
	                      std::map<unsigned short, unsigned short>& varMap) {
		std::map<unsigned short, unsigned short> invVarMap{ };
		int n = in.p->v;
		Edge root{in};

		if (n<1) return in;

		computeMatrixProperties = Disabled;
		for (const auto& i : varMap) invVarMap[i.second] = i.first;

		auto min = activeNodeCount;
		for (int i = 1; i <= n; i++) {
			exchangeBaseCase(i);

			if (min > activeNodeCount) {
				min = activeNodeCount;

				auto temp = varMap[invVarMap[i]];
				varMap[invVarMap[i]] = varMap[invVarMap[i+1]];
				varMap[invVarMap[i+1]] = temp;
			} else {
				exchangeBaseCase(i);
			}

			// there are nodes which need to renormalized
			if (unnormalizedNodes > 0) {
				auto oldroot = root;
				root = renormalize(root);
				incRef(root);
				decRef(oldroot);
				in.p = root.p;
				in.w = root.w;
				if (unnormalizedNodes > 0) {
					std::cerr << "Renormalization failed. " << unnormalizedNodes << " nodes remaining." << std::endl;
				}
			}
			computeMatrixProperties = Enabled;
			markForMatrixPropertyRecomputation(root);
			recomputeMatrixProperties(root);
		}
		return in;
	}

	/// Tries all permutations in a window of size 3.
	/// Permutation with lowest node count is choosen.
	/// Shifts this window from the bottom to the top.
	/// \param in decision diagram to operate on
	/// \param varMap stores the variable mapping (cf. dynamicReorder(...))
	/// \return the resulting decision diagram (and the changed varMap, which is returned as reference)
	Edge Package::window3(Edge in,
	                      std::map<unsigned short, unsigned short>& varMap) {
		std::map<unsigned short, unsigned short> invVarMap{ };
		int n = in.p->v;
		Edge root{in};

		if (n<2) return window2(in, varMap);

		computeMatrixProperties = Disabled;
		for (const auto& i : varMap) invVarMap[i.second] = i.first;

		for (int i = 0; i + 1 < n; i++) {
			int x = i;
			int y = x + 1;
			int z = y + 1;
			auto min = activeNodeCount;
			int best = 1;  // ABC

			exchange(x, y);  // BAC
			auto tempVar = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = tempVar;
			if (min > activeNodeCount) {
				best = 2;
				min = activeNodeCount;
			}

			exchange(y, z);  // BCA
			tempVar = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = tempVar;
			if (min > activeNodeCount) {
				best = 3;
				min = activeNodeCount;
			}

			exchange(x, y);  // CBA
			tempVar = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = tempVar;
			if (min > activeNodeCount) {
				best = 4;
				min = activeNodeCount;
			}

			exchange(y, z);  // CAB
			tempVar = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = tempVar;
			if (min > activeNodeCount) {
				best = 5;
				min = activeNodeCount;
			}

			exchange(x, y);  // ACB
			tempVar = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = tempVar;
			if (min > activeNodeCount) {
				best = 6;
				min = activeNodeCount;
			}

			switch (best) {
				case 3:  // BCA
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case 4:  // CBA
					exchange(x, y);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case 1:  // ABC
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case 6:  // ACB
					break;
				case 2:  // BAC
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case 5:  // CAB
					exchange(x, y);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				default:
					break;
			}

			// there are nodes which need to renormalized
			if (unnormalizedNodes > 0) {
				auto oldroot = root;
				root = renormalize(root);
				incRef(root);
				decRef(oldroot);
				in.p = root.p;
				in.w = root.w;
				if (unnormalizedNodes > 0) {
					std::cerr << "Renormalization failed. " << unnormalizedNodes << " nodes remaining." << std::endl;
				}
			}
			computeMatrixProperties = Enabled;
			markForMatrixPropertyRecomputation(root);
			recomputeMatrixProperties(root);
		}
		return in;
	}

	/// Tries all permutations in a window of size 4.
	/// Permutation with lowest node count is choosen.
	/// Shifts this window from the bottom to the top.
	/// \param in decision diagram to operate on
	/// \param varMap stores the variable mapping (cf. dynamicReorder(...))
	/// \return the resulting decision diagram (and the changed varMap, which is returned as reference)
	Edge Package::window4(Edge in,
	                      std::map<unsigned short, unsigned short>& varMap) {
		std::map<unsigned short, unsigned short> invVarMap{ };
		int n = in.p->v;
		Edge root{in};

		if (n<3) return window3(in, varMap);

		computeMatrixProperties = Disabled;
		for (const auto& i : varMap) invVarMap[i.second] = i.first;

		for (int i = 0; i + 2 < n; i++) {
			int w = i;
			int x = w + 1;
			int y = x + 1;
			int z = y + 1;
			int best;
			auto min = activeNodeCount;

			#define ABCD 1
			best = ABCD;

			#define BACD 7
			exchange(w, x);
			auto tempVar = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = tempVar;
			if (min > activeNodeCount) {
				best = BACD;
				min = activeNodeCount;
			}

			#define BADC 13
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = BADC;
				min = activeNodeCount;
			}

			#define ABDC 8
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = ABDC;
				min = activeNodeCount;
			}

			#define ADBC 14
			exchange(x, y);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = ADBC;
				min = activeNodeCount;
			}

			#define ADCB 9
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = ADCB;
				min = activeNodeCount;
			}

			#define DACB 15
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = DACB;
				min = activeNodeCount;
			}

			#define DABC 20
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = DABC;
				min = activeNodeCount;
			}

			#define DBAC 23
			exchange(x, y);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = DBAC;
				min = activeNodeCount;
			}

			#define BDAC 19
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = BDAC;
				min = activeNodeCount;
			}

			#define BDCA 21
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = BDCA;
				min = activeNodeCount;
			}

			#define DBCA 24
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = DBCA;
				min = activeNodeCount;
			}

			#define DCBA 22
			exchange(y, x);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = DCBA;
				min = activeNodeCount;
			}

			#define DCAB 18
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = DCAB;
				min = activeNodeCount;
			}

			#define CDAB 12
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = CDAB;
				min = activeNodeCount;
			}

			#define CDBA 17
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = CDBA;
				min = activeNodeCount;
			}

			#define CBDA 11
			exchange(x, y);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = CBDA;
				min = activeNodeCount;
			}

			#define BCDA 16
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = BCDA;
				min = activeNodeCount;
			}

			#define BCAD 10
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = BCAD;
				min = activeNodeCount;
			}

			#define CBAD 5
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = CBAD;
				min = activeNodeCount;
			}

			#define CABD 3
			exchange(y, x);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = CABD;
				min = activeNodeCount;
			}

			#define CADB 6
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = CADB;
				min = activeNodeCount;
			}

			#define ACDB 4
			exchange(w, x);
			tempVar = varMap[invVarMap[w]];
			varMap[invVarMap[w]] = varMap[invVarMap[x]];
			varMap[invVarMap[x]] = tempVar;
			if (min > activeNodeCount) {
				best = ACDB;
				min = activeNodeCount;
			}

			#define ACBD 2
			exchange(y, z);
			tempVar = varMap[invVarMap[y]];
			varMap[invVarMap[y]] = varMap[invVarMap[z]];
			varMap[invVarMap[z]] = tempVar;
			if (min > activeNodeCount) {
				best = ACBD;
				min = activeNodeCount;
			}


			switch (best) {
				case DBCA:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case BDCA:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case CDBA:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
				case ADBC:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case ABDC:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case ACDB:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case ACBD:
					break;
				case DCBA:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case BCDA:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case CBDA:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
					break;
				case DBAC:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case DCAB:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
				case DACB:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case BACD:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case CABD:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
					break;
				case DABC:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case BADC:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case CADB:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
					break;
				case BDAC:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case CDAB:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
				case ADCB:
					exchange(y, z);
					tempVar = varMap[invVarMap[z]];
					varMap[invVarMap[z]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case ABCD:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
					break;
				case BCAD:
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
				case CBAD:
					exchange(w, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[w]];
					varMap[invVarMap[w]] = tempVar;
					exchange(y, x);
					tempVar = varMap[invVarMap[x]];
					varMap[invVarMap[x]] = varMap[invVarMap[y]];
					varMap[invVarMap[y]] = tempVar;
					break;
				default:
					break;
			}

			// there are nodes which need to renormalized
			if (unnormalizedNodes > 0) {
				auto oldroot = root;
				root = renormalize(root);
				incRef(root);
				decRef(oldroot);
				in.p = root.p;
				in.w = root.w;
				if (unnormalizedNodes > 0) {
					std::cerr << "Renormalization failed. " << unnormalizedNodes << " nodes remaining." << std::endl;
				}
			}
			computeMatrixProperties = Enabled;
			markForMatrixPropertyRecomputation(root);
			recomputeMatrixProperties(root);
		}
		return in;
	}

}
