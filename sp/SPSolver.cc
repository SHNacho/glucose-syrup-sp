#include <algorithm>
#include <iostream>
#include "SPSolver.h"

using namespace std;

namespace sp{

	SPSolver::SPSolver(FactorGraph* fg, float alpha){
		this->fg = fg;
		rng = default_random_engine {};
		time_t current_time = time(NULL);
		rng.seed(current_time);
		this->alpha = alpha;
		this-> SPIter = 0;
		this->WS_MAX_STEPS = 100 * fg->variables.size();
		this->initRandomSurveys();
	}

	double SPSolver::iterate(){
		double eps=0.0, maxeps=0.0;

		vector<Clause*> clauses = this->fg->clauses;
		shuffle(clauses.begin(), clauses.end(), this->rng);

		for(Clause* c : clauses) if(!c->satisfied){
			eps = updateSurvey(c);	
			if(eps > maxeps)
				maxeps = eps;
		}

		return maxeps;
	}

	double SPSolver::updateSurvey(Clause* c){
		double u;	
		double s;	
		double pu, ps, pz;
		vector<double> prods;
		double allprod = 1.0;
		int zeroes = 0;
		double eps;

		for(Literal* l : c->literals){
			Variable* var = l->var;
			if(l->enabled && var->value==0){
				//	Si type = -1 : V_a^u(j) = V_+(j) ; V_a^s(j) = V_-(j) \ a
				//	Si type =  1 : V_a^u(j) = V_-(j) ; V_a^s(j) = V_+(j) \ a
				//	var->m  --> Pi€V_+(j) (1-eta)
				//	var->p  --> Pi€V_-(j) (1-eta)
				if(l->type < 0){ // Si el literal es negativo
					u = var->mzero ? 0 : var->m; // Pi€V_a^u(j) (1-eta)
					// Pi€V_a^s(j) (1-eta)
					if(var->pzero == 0)
						s = var->p / (1 - l->survey); 
					else if(var->pzero == 1 && (1 - l->survey) < EPS)
						s = var->p;
					else
						s = 0.0;
				} else { // Si el literal es positivo
					u = var->pzero ? 0.0 : var->p; // Pi€V_a^u(j) (1-eta)
					// Pi€V_a^s(j) (1-eta)
					if(var->mzero == 0)
						s = var->m / (1.0 - l->survey);
					else if (var->mzero == 1 && (1.0 - l->survey) < EPS)
						s = var->m;
					else
						s = 0.0;
				}	

				pu = (1 - u) * s;
				ps = (1 - s) * u;
				pz = s * u;


				double prod;
				if (pu == 0){
					prod = 0.0;
				} else {
					prod = pu / (pu + ps + pz);
				}

				prods.push_back(prod);

				if(prod < EPS){
					if(++zeroes == 2)
						break;
				} else {
					allprod *= prod;
				}
			}
		}

		int i = 0;
		eps = 0.0;
		for(Literal* l : c->literals){ 
			Variable* var = l->var;
			if(l->enabled && var->value==0){
				double newsurvey = 0.0;
				if(!zeroes){
					newsurvey = allprod / prods[i];
				} else if(zeroes == 1 && prods[i] < EPS) {
					newsurvey = allprod;
				} else {
					newsurvey = 0.0;
				}

				if(l->type < 0){
					if(1.0 - l->survey > EPS) {
						if(1.0 - newsurvey > EPS) {
							var->p *= ((1.0 - newsurvey) / ( 1.0 - l->survey));
						} else {
							var->p /= (1.0 - l->survey);
							var->pzero++;
						} 
					} else {
						if(1-newsurvey > EPS) {
							var->p *= (1.0 - newsurvey);
							var->pzero--;
						} 
					}
				} else {
					if(1 - l->survey > EPS){
						if(1.0 - newsurvey > EPS){
							var->m *= ((1.0 - newsurvey) / (1.0 - l->survey));
						} else {
							var->m /= (1.0 - l->survey);
							var->mzero++;
						}
					} else {
						if(1 - newsurvey > EPS){
							var->m *= (1.0 - newsurvey);
							var->mzero--;
						}
					}
				}

				double diff = abs(l->survey - newsurvey);
	      		if (eps < diff)
	        		eps = abs(diff);

	      		l->survey = newsurvey;
	      		i++;
			}
		}
		return eps;
	}

	bool SPSolver::surveyPropagation(){
		double eps = 0;
		int iter = 0;
		computeSubProducts();
		do{
			SPIter++;
			eps = iterate();
		} while((eps > EPSILON) && (iter++ < ITERATIONS));
		if(eps <= EPSILON){
			return true;
		} else {
			return false;
		}
	}


	void SPSolver::computeSubProducts(){
		for (Variable* v : fg->variables) if (v->value == 0){
			v->p = 1.0;
			v->m = 1.0;
			v->pzero = 0;
			v->mzero = 0;

			for (Literal* l : v->literals) if(!l->cl->satisfied){
				if(l->type < 0){ // Calcula los productos 1-eta de los literales negativos
					if(1 - l->survey > EPS){
						v->p *= 1 - l->survey;
					} else {
						v->pzero++;
					}
				} else { // Calcula los productos de 1 - eta de los literales positivos
					if(1 - l->survey > EPS){
						v->m *= 1 - l->survey;
					} else {
						v->mzero++;
					}
				}

			}
		}
	}


	void SPSolver::computeBias(Variable* var){
		double p, m;
		p = var->pzero ? 0 : var->p;
		m = var->mzero ? 0 : var->m;

		var->wz = p*m;
		var->wp = m - var->wz;
		var->wm = p - var->wz;

		// Normalización de los sesgos
		double norm = var->wm + var->wz + var->wp;
		var->wm /= norm;
		var->wp /= norm;
		var->wz /= norm;
	}

	void SPSolver::computeBias(int id_var){
		computeBias(fg->variables[id_var - 1]);
	}

	int SPSolver::valueToAssign(int id_var){
		Variable* var = fg->variables[id_var-1];
		int val = var->wp > var->wm ? -1 : 1;
	}


	void SPSolver::unitPropagation(){
		for (Clause* c : fg->clauses){
			if(c->unassigned_literals == 1 && !c->satisfied){
				fg->fixUnitClause(c);
			}
		}
	}

	void SPSolver::initRandomSurveys(){
		std::uniform_real_distribution<float> distribution(0.0, 1.0);
		for(Literal* l : fg->literals){
			if(l->enabled){
				l->survey = distribution(rng);
			}
		}
	}

	bool SPSolver::surveyInspiredDecimation(){
		int SIDIterations = 0;
		SPIter = 0;

		// Se realiza unitPropagation por si hay cláusulas unitarias
		unitPropagation();

		// Se inicializan las surveys
		initRandomSurveys();

		// Se cualculan cuantas variables se asignarán en cada paso
		int fixPerStep = fg->variables.size() * alpha > 1 ? fg->unassigned_vars * alpha : 1;

		// Mientras que survey propagation llegue a un estado de convergencia
		while(surveyPropagation() && fg->unassigned_vars){
			SIDIterations++;

			double summag = 0;		// Suma de los sesgos
			double maxmag; 			// Máximo sesgo obtenido

			// Se calcula el sesgo de cada la variable
			for(Variable* v : fg->variables) if(v->value == 0){
				computeBias(v);
				maxmag=v->wp > v->wm ? v->wp : v->wm;
				summag += maxmag;
			}

			// Se ordenan las variables en función del sesgo
			vector<Variable*> sortedVars = fg->variables;
			std::sort(sortedVars.begin(), sortedVars.end(), biasComparator);

			// Si se llega a un estado paramagnético, se resuelve por walksat
			if(summag/fg->unassigned_vars < PARAMAGNET){
				//WALKSAT
				WalkSat();
				return true;
			}

			// Asignación de las variables ordenadas por bias
			int aux = fixPerStep;
			while(fg->unassigned_vars && aux--){
				vector<Variable*>::iterator it = sortedVars.begin();
				while((*it)->value && it != sortedVars.end())
					it++;
				// Una asignación modifica el sesgo de las demás 
				// variables por lo que se recalcula
				computeBias(*it);
				int val = (*it)->wp > (*it)->wm ? -1 : 1;
				if (!fg->fix(*it, val, true))
					return false;

				it++;
			}
		}

		if (fg->unassigned_vars == 0)
			return true;
		else
			return false;
	}

	bool SPSolver::varsToAssign(){
		while(!fg->fixedVars.empty()) fg->fixedVars.pop();
		// Se cualculan cuantas variables se asignarán en cada paso
		int fixPerStep = fg->variables.size() * alpha > 1 ? fg->unassigned_vars * alpha : 1;
		if (surveyPropagation() && fg->unassigned_vars){
			double summag = 0;		// Suma de los sesgos
			double maxmag; 			// Máximo sesgo obtenido

			// Se calcula el sesgo de cada la variable
			for(Variable* v : fg->variables) if(v->value == 0){
				computeBias(v);
				maxmag=v->wp > v->wm ? v->wp : v->wm;
				summag += maxmag;
			}

			// Se ordenan las variables en función del sesgo
			vector<Variable*> sortedVars = fg->variables;
			std::sort(sortedVars.begin(), sortedVars.end(), biasComparator);

			// Si se llega a un estado paramagnético, se resuelve por walksat
			if(summag/fg->unassigned_vars < PARAMAGNET){
				//WALKSAT
				cout << "Iteraciones de SP: " << SPIter << endl;
				cout << "WALKSAT" << endl;
				return WalkSat();
			}

			// Asignación de las variables ordenadas por bias
			int aux = fixPerStep;

			while(fg->unassigned_vars && aux--){
				vector<Variable*>::iterator it = sortedVars.begin();
				while((*it)->value && it != sortedVars.end())
					it++;
				// Una asignación modifica el sesgo de las demás 
				// variables por lo que se recalcula
				computeBias(*it);
				int val = (*it)->wp > (*it)->wm ? -1 : 1;
				if (!fg->fix(*it, val, true))
					return false;

				it++;
			}

			return true;
		}

		return false;
	}

	bool SPSolver::WalkSat()
	{
		vector<Variable *> w_variables;
		vector<Clause *> w_clauses;
		for (Variable *v : fg->variables)
		{
			if (v->value == 0)
				w_variables.push_back(v);
		}
		for (Clause *c : fg->clauses)
		{
			if (!c->satisfied)
				w_clauses.push_back(c);
		}


		vector<Clause *> unsatClauses;
		for (int t = 0; t < WS_MAX_TRIES; t++)
		{
			// Assign all Varibles with random values
			for (Variable *var : w_variables)
			{
				int values[2] = {1, -1}; // Posibles valores
				std::uniform_int_distribution<int> int_distribution(0, 1);
				var->value = values[int_distribution(rng)];
			}

			// Separate unsat clauses
			unsatClauses.clear();
			for (Clause *clause : w_clauses)
			{
				if (clause->countTrueLiterals() == 0)
					unsatClauses.push_back(clause);
			}

			for (int f = 0; f < WS_MAX_STEPS; f++)
			{
				// If there are no unsat clauses, subgraph is solved and it's SAT
				if (unsatClauses.size() == 0){
					for(Variable* v : w_variables){
						pair<int, int> var_value(v->id, v->value);
						fg->fixedVars.push(var_value);
					}
					return true;
				}

				// Select random unsat clause
				std::uniform_int_distribution<> randomInt(0, unsatClauses.size() - 1);
				int randIndex = randomInt(rng);
				Clause *selectedClause = unsatClauses[randIndex];
				std::vector<Literal *> selectedClauseLits;
				for(Literal* l : selectedClause->literals) if(l->enabled)
					selectedClauseLits.push_back(l);

				// -----------------------------------------------------------------------
				// For each variable in selected clause, calculate break-count (number of
				// currently satisfied clauses that become unsatisfied if the variable
				// value is fliped) and store lowest break-count
				// Fast-walksat is used to compute break-count
				// -----------------------------------------------------------------------
				vector<Variable *> lowestBreakCountVar;
				int lowestBreakCount = fg->variables.size() * alpha + 1;
				for (Literal *edge : selectedClauseLits)
				{
					int breakCount = 0;
					for (Literal *e : edge->var->literals)
					{
						// Only clauses that are satisfied by the var and have only one
						// literal will become unsat
						if (e->enabled && edge->var->value == e->type &&
							e->cl->trueLiterals == 1)
							breakCount++;

						// TODO: Remove old way of computing break-count
						// if (e->clause->IsSAT()) {
						//   edge->variable->AssignValue(!edge->variable->value);
						//   if (!e->clause->IsSAT()) breakCount++;
						//   edge->variable->AssignValue(!edge->variable->value);
						// }
					}

					// Update lowest break-count
					if (breakCount == lowestBreakCount)
						lowestBreakCountVar.push_back(edge->var);
					if (breakCount < lowestBreakCount)
					{
						lowestBreakCountVar.clear();
						lowestBreakCountVar.push_back(edge->var);
						lowestBreakCount = breakCount;
					}
				}

				// -----------------------------------------------------------------------
				// Select the variable of the clause that has break-count = 0
				// If not, with probability p (noise), flip a random variable and
				// with probability 1 - p, flip the variable with lowest break-count
				// -----------------------------------------------------------------------
				Variable *var = nullptr;
				// Select the var with lower break-count with probability 1 - p or force
				// it if break-count == 0
				// If multiple vars have same breack-count, select randomly
				std::uniform_real_distribution<> randomReal(0, 1);
				if (lowestBreakCount == 0 || randomReal(rng) > WS_NOISE)
				{
					if (lowestBreakCountVar.size() == 1)
					{
						var = lowestBreakCountVar[0];
					}
					else
					{
						uniform_int_distribution<> randi(0, lowestBreakCountVar.size() - 1);
						int i = randi(rng);
						var = lowestBreakCountVar[i];
					}
				}
				// Select random var with probability p
				else
				{
					std::uniform_int_distribution<> randEdgeIndexDist(
						0, selectedClauseLits.size() - 1);
					int randomEdgeIndex = randEdgeIndexDist(rng);
					var = selectedClauseLits[randomEdgeIndex]->var;
				}

				// -----------------------------------------------------------------------
				// Flip de selected variable and update unsatClause list by removing all
				// unsat clauses where the variable appear, flip it and then, add the new
				// unsat clauses
				// -----------------------------------------------------------------------
				for (Literal *e : var->literals)
				{
					if (e->enabled && e->cl->trueLiterals == 0)
					{
						unsatClauses.erase(
							find(unsatClauses.begin(), unsatClauses.end(), e->cl));
					}
				}

				// Flip
				var->value = var->value == 1 ? -1 : 1;

				for (Literal *e : var->literals)
				{
					if (e->enabled && e->cl->countTrueLiterals() == 0)
						unsatClauses.push_back(e->cl);
				}
			}
		}

		// 2. If a sat assignment was not found, return false.
		return false;
	}

	Variable* SPSolver::pickVar(Clause* cl){

		vector<Variable*> vars;
		for(Literal* l : cl->literals) if(l->var->ws)
			vars.push_back(l->var);

		// Se ordenan las variables de manera aleatoria
		shuffle(vars.begin(), vars.end(), this->rng);

		// Separating-non-caching - Sixue Liu 2015
		for(Variable* v : vars){
			vector<Clause*> tlc = v->TLC();
			for(Clause* c : tlc){
				c->ws_unvisited = true;
			}
			int zero = true;
			for(Clause* c : tlc){
				c->ws_unvisited = false;
				if(c->NT() == 1){
					zero = false;
					break;
				}
			}
			if(zero) return v;
		}

		for(Variable* v : vars){
			v->ws_break = 1;
			vector<Clause*> tlc = v->TLC();
			for(Clause* c : tlc) if(c->ws_unvisited){
				if(c->NT() == 1)
					v->ws_break += 1;
			}
		}

		std::uniform_real_distribution<float> float_distribution(0.0, 1.0);
		std::uniform_int_distribution<int> int_distribution(0, vars.size() - 1);
		float p = float_distribution(rng);
		if(p < WS_NOISE){
			int idx = int_distribution(rng);
			Variable* ret_var = vars[idx];
			return ret_var;
		}
		else{
			Variable* min_break_var = vars[0];
			int min_break = 1000;
			for(Variable* v : vars){
				int var_break = v->ws_break;
				if(var_break < min_break){
					min_break = var_break;
					min_break_var = v;
				}
			}
			return min_break_var;
		}

	}

	void SPSolver::resetGraph(){
		for(Clause* c : fg->clauses){
			c->satisfied = false;
			c->unassigned_literals = c->literals.size();
		}
		for(Literal* l : fg->literals){
			l->enabled = true;
		}
		for(Variable* v : fg->variables){
			v->value = 0;
		}
		while(!fg->fixedVars.empty()) fg->fixedVars.pop();
		fg->unassigned_vars = fg->variables.size();
		initRandomSurveys();
	}

	bool biasComparator(Variable* v1, Variable* v2){
		double b1 = fabs(v1->wm - v1->wp);
		double b2 = fabs(v2->wm - v2->wp);
		return (b1 > b2);
	}

}
