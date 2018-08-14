package za.ac.sun.cs.green.service.simplify;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealConstant;
import za.ac.sun.cs.green.expr.RealVariable;
import za.ac.sun.cs.green.expr.StringConstant;
import za.ac.sun.cs.green.expr.StringVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.BasicService;

public class ConstantPropogation extends BasicService {
	
	private StoredInfo binTree;
	private boolean altered = false;
	
	private final Constant TF0 = new IntConstant(0);
	private final Constant TF1 = new IntConstant(1);
	
	public ConstantPropogation(Green solver) {
		super(solver);
	}
	
	@Override
	public Set<Instance> processRequest(Instance instance) {
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(getClass());
		if (result == null) {
			final Expression e =  propagate(instance.getFullExpression());
			final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
			result = Collections.singleton(i);
			instance.setData(getClass(), result);
		}
		return result;
	}
	
	
	
	public Expression propagate(Expression expression) {
		Operation op = (Operation) expression;
		//System.out.println("Before: " + op);
		try {
		op.accept(new binTreeVisitor());
		do {
			altered = false;
			binTree.simplifyTree();
		} while (altered);
		} catch (Exception ex) {
			ex.printStackTrace();
		}
		//System.out.println("After: " + binTree.ownedExp);
		return binTree.ownedExp;
	}
	
	private class StoredInfo {
		public HashMap<Variable, Expression> knownVars;
		public HashSet<Variable> noReplaceVars;
		public StoredInfo parent;
		public ArrayList<StoredInfo> children;
		public Expression ownedExp;
		public Operation.Operator op;
		public boolean alteredExp = false;
		public boolean alteredKnownVals = false;
		
		public StoredInfo (StoredInfo parent) {
			this.parent = parent;
			if (parent != null) {
				knownVars = parent.knownVars;//new HashMap<Variable, Expression> ();
			} else {
				knownVars = new HashMap<Variable, Expression> ();
			}
			children = new ArrayList<StoredInfo>();
			noReplaceVars = new HashSet<Variable>();
			ownedExp = null;
			op = null;
		}
		
		public int getArity() {
			return children.size();
		}
		
		public boolean propagateChild (StoredInfo child) {
			children.add(child);
			return true;
		}
		
		private void genExpFromChildren () {
			if ((op != null) && (children.size() == 2)) {
				int arity = op.getArity();
				ownedExp = new Operation(op, children.get(0).ownedExp, children.get(1).ownedExp);
				////System.out.println(ownedExp);
				if (parent != null) {
					parent.genExpFromChildren();
				}
				/*if (children.get(0).alteredExp == true) {
					children.get(0).alteredExp = false;
				}
				if (children.get(1).alteredExp == true) {
					children.get(1).alteredExp = false;
				}*/
			}
		}
		
		private boolean canOrder(Operation.Operator op) {
			switch (op) {
			case EQ:
				return true;
			case ADD:
				return true;
			case MUL:
				return true;
			}
			return false;
		}
		
		private void orderEQ() {
			if (canOrder(op) && (children.size() == 2 )){
					if ((children.get(0).ownedExp instanceof Constant) && !(children.get(1).ownedExp instanceof Constant)) {
						StoredInfo temp = children.get(1);
						children.set(1, children.get(0));
						children.set(0, temp);
						genExpFromChildren();
						altered = true;
					}
			}
		}
		
		private boolean isCalcOp(Operation.Operator op) {
			if (op == null) {
				return false;
			}
			if (op.ordinal() >= Operation.Operator.ADD.ordinal() && op.ordinal() <= Operation.Operator.DIV.ordinal()) {
				return true;
			}
			return false;
		}
		
		private boolean isRelOp(Operation.Operator op) {
			if (op == null) {
				return false;
			}
			if (op.ordinal() >= Operation.Operator.EQ.ordinal() && op.ordinal() <= Operation.Operator.GE.ordinal()) {
				return true;
			}
			return false;
		}
		
		private boolean isTrue() {
			if (op == Operation.Operator.EQ) {
				if ((children.get(0).ownedExp == TF0) && (children.get(1).ownedExp == TF0)){
					return true;
				}
			}
			return false;
		}
		
		private boolean isFalse() {
			if (op == Operation.Operator.EQ) {
				if ((children.get(0).ownedExp == TF0) && (children.get(1).ownedExp == TF1)){
					return true;
				}
			}
			return false;
		}
		
		private void morphOpTrue() {
			if (!isTrue()) {
				altered = true;
			}
			StoredInfo lc = new StoredInfo(this), rc = new StoredInfo(this);
			lc.ownedExp = TF0;
			rc.ownedExp = TF0;
			op = Operation.Operator.EQ;
			children.clear();
			children.add(lc);
			children.add(rc);
			genExpFromChildren();
		}
		
		private void morphOpFalse() {
			if (!isFalse()) {
				altered = true;
			}
			StoredInfo lc = new StoredInfo(this), rc = new StoredInfo(this);
			lc.ownedExp = TF0;
			rc.ownedExp = TF1;
			op = Operation.Operator.EQ;
			children.clear();
			children.add(lc);
			children.add(rc);
			
			genExpFromChildren();
		}
		
		private double getValue(Constant c) {
			double ret = 1.0/0.0;
			if (c instanceof IntConstant) {
				ret = ((IntConstant)c).getValue();
			} else if (c instanceof RealConstant){
				ret = ((RealConstant)c).getValue();
			}
			return ret;
		}
		
		private Operation.Operator getInverseOp(Operation.Operator op) {
			if (op == Operation.Operator.ADD) {
				return Operation.Operator.SUB;
			}
			if (op == Operation.Operator.SUB) {
				return Operation.Operator.ADD;
			}
			if (op == Operation.Operator.MUL) {
				return Operation.Operator.DIV;
			}
			if (op == Operation.Operator.DIV) {
				return Operation.Operator.MUL;
			}
			return null;
		}
		
		
		private Constant doCalc (Operation.Operator op, Constant lOperhand, Constant rOperhand) {
			boolean hasDouble = false;
			double lVal, rVal, sol = 0;
			Constant newC = null;
			if (lOperhand instanceof IntConstant) {
				lVal = ((IntConstant)lOperhand).getValue();
			} else {
				lVal = ((RealConstant)lOperhand).getValue();
				hasDouble = true;
			}
			if (rOperhand instanceof IntConstant) {
				rVal = ((IntConstant)rOperhand).getValue();
			} else {
				rVal = ((RealConstant)rOperhand).getValue();
				hasDouble = true;
			}
			switch (op) {
			case ADD:
				sol = lVal + rVal;
				////System.out.println("Added, sol: " + sol);
				break;
			case SUB:
				sol = lVal - rVal;
				////System.out.println("Sub, sol: " + sol);
				break;
			case MUL:
				sol = lVal * rVal;
				////System.out.println("Mul, sol: " + sol);
				break;
			case DIV:
				sol = lVal / rVal;
				////System.out.println("Div, sol: " + sol);
			}
			if (hasDouble || ((int)sol != sol)) {
				newC = new RealConstant(sol);
			} else {
				newC = new IntConstant((int)sol);
			}
			
			return newC;
		}
		
		private boolean hasFloatableConstant() {
			if (isCalcOp(op)) {
				return false;
			}
			return false;
		}
		
		private void attemptConstantFloatParent() {
		}
		
		private void updateKnownVars() {
			if (op == Operation.Operator.EQ) {
				Expression oper1 = children.get(0).ownedExp, oper2 = children.get(1).ownedExp;
				if ((oper1 instanceof Variable) && (oper2 instanceof Constant)) {
					Expression exp = knownVars.putIfAbsent((Variable)oper1, (Constant)oper2);
					if (exp == null) {
						altered = true;
						children.get(0).noReplaceVars.add((Variable)oper1);
					}
				}
			}
			
		}
		
		private void attemptConstantFloat() {
			StoredInfo parent = this.parent;
			
			if (parent != null) {
				Operation.Operator pOp = parent.op;
				if ((parent.children.get(0) == this) && (isRelOp(pOp))) {
					Expression possibleC = this.children.get(1).ownedExp;
					if ((possibleC instanceof Constant) && (isCalcOp(op))) {
						Expression newExp = new Operation (getInverseOp(op), parent.children.get(1).ownedExp, possibleC);
						StoredInfo newInfo = new StoredInfo(parent);
						StoredInfo constantInfo = new StoredInfo(newInfo);
						constantInfo.ownedExp = possibleC;
						newInfo.ownedExp = newExp;
						newInfo.op = getInverseOp(op);
						newInfo.children.add(parent.children.get(1));
						newInfo.children.add(constantInfo);
						parent.children.set(1, newInfo);
						parent.children.set(0, children.get(0));
						parent.genExpFromChildren();
						children.clear();
						altered = true;
					}
				}
			}
		}
		
		public void simplifyTree() {
			for (int i = 0; i < children.size(); i++) {
				children.get(i).simplifyTree();
			}
			
			if (ownedExp instanceof Operation) {
				
				//System.out.println("Operation found: " + ownedExp);
				//System.out.println("Known Vars: " + knownVars);
				Operation.Operator op = ((Operation) ownedExp).getOperator();
				if ((children.get(0).ownedExp instanceof Constant) && (children.get(1).ownedExp instanceof Constant)) {
					Constant c1 = (Constant)children.get(0).ownedExp, c2 = (Constant)children.get(1).ownedExp;
					////System.out.println("Double Constants found: " + ownedExp);
					if (isCalcOp(op)) {
						ownedExp = doCalc(op, c1, c2);
						//System.out.println("New Constant: " + ownedExp);
						op = null;
						children.clear();
						////System.out.println("Starting genExp");
						altered = true;
						parent.genExpFromChildren();
						////System.out.println("Finished genExp");
						
					} else if (op == Operation.Operator.EQ) {
						if ((c1 != TF0) || !((c2 == TF0) || (c2 == TF1))) {
							altered = true;
						}
						//c1 = TF0;
						if (c1.equals(c2)) {
							c1 = TF0;
							c2 = TF0;
						} else {
							c1 = TF0;
							c2 = TF1;
						}
						children.get(0).ownedExp = c1;
						children.get(1).ownedExp = c2;
						//altered = true;
						genExpFromChildren();
					} else if (op == Operation.Operator.LE) {
						if (getValue(c1) <= getValue(c2)) {
							morphOpTrue();
						} else {
							morphOpFalse();
						}
					} else if (op == Operation.Operator.LT) {
						if (getValue(c1) < getValue(c2)) {
							morphOpTrue();
						} else {
							morphOpFalse();
						}
					} else if (op == Operation.Operator.GE) {
						if (getValue(c1) >= getValue(c2)) {
							morphOpTrue();
						} else {
							morphOpFalse();
						}
					} else if (op == Operation.Operator.GT) {
						if (getValue(c1) > getValue(c2)) {
							morphOpTrue();
						} else {
							morphOpFalse();
						}
					}
					
				} else /*if ((children.get(0).op == Operation.Operator.EQ) && (children.get(1).op == Operation.Operator.EQ))*/{
					if (op == Operation.Operator.AND) {
						if (children.get(0).isFalse() || children.get(1).isFalse()) {
							morphOpFalse();
						} else if (children.get(0).isTrue() && children.get(1).isTrue()) {
							morphOpTrue();
						} else if (children.get(0).isTrue()) {
							altered = true;
							int parentIndex = 0;
							if (parent.children.get(0) != this) {
								parentIndex = 1;
							}
							parent.children.set(parentIndex, children.get(1));
							parent.genExpFromChildren();
						} else if (children.get(1).isTrue()) {
							altered = true;
							int parentIndex = 0;
							if (parent.children.get(0) != this) {
								parentIndex = 1;
							}
							parent.children.set(parentIndex, children.get(0));
							parent.genExpFromChildren();
						}
					} else if (op == Operation.Operator.OR) {
						if (children.get(0).isFalse() && children.get(1).isFalse()) {
							morphOpFalse();
						} else if (children.get(0).isTrue() && children.get(1).isTrue()) {
							morphOpTrue();
						}
					} 
				} 
				if (op != null) {
					orderEQ();
					updateKnownVars();
					attemptConstantFloat();
					genExpFromChildren();
				}
				
			} else if (ownedExp instanceof Variable) {
				Variable var = (Variable)ownedExp;
				if (!noReplaceVars.contains(var)) {
					Expression value = knownVars.get(var);
					if (value != null) {
						ownedExp = value;
						altered = true;
						//parent.genExpFromChildren();
					}
				}
			}
		}
	}
	
	public class binTreeVisitor extends Visitor {

		
		public StoredInfo info = null;
		//public boolean altered = false;
		
		public void preVisit(Constant constant) throws VisitorException {
			preVisit((Expression) constant);
		}

		@SuppressWarnings("unchecked")
		public void preVisit(Expression expression) throws VisitorException {
			StoredInfo newInfo = new StoredInfo(info);
			if (info != null) {
				info.propagateChild(newInfo);
				//newInfo.knownVars = info.knownVars;
			}
			info = newInfo;
		}

		public void preVisit(IntConstant intConstant) throws VisitorException {
			preVisit((Constant) intConstant);
		}

		public void preVisit(IntVariable intVariable) throws VisitorException {
			preVisit((Variable) intVariable);
		}

		public void preVisit(Operation operation) throws VisitorException {
			
			preVisit((Expression) operation);
			info.op = operation.getOperator();
			
			
		}

		public void preVisit(RealConstant realConstant) throws VisitorException {
			preVisit((Constant) realConstant);
		}

		public void preVisit(RealVariable realVariable) throws VisitorException {
			preVisit((Variable) realVariable);
		}

		public void preVisit(StringConstant stringConstant) throws VisitorException {
			preVisit((Constant) stringConstant);
		}

		public void preVisit(StringVariable stringVariable) throws VisitorException {
			preVisit((Variable) stringVariable);
		}

		public void preVisit(Variable variable) throws VisitorException {
			preVisit((Expression) variable);
		}

		public void postVisit(Constant constant) throws VisitorException {
			info.ownedExp = constant;
			postVisit((Expression) constant);
		}

		public void postVisit(Expression expression) throws VisitorException {
			
			if (info.parent != null) {
				info = info.parent;
			} else {
				////System.out.println(info.ownedExp);
				binTree = info;
			}
		}

		public void postVisit(IntConstant intConstant) throws VisitorException {
			postVisit((Constant) intConstant);
		}

		public void postVisit(IntVariable intVariable) throws VisitorException {
			postVisit((Variable) intVariable);
		}

		public void postVisit(Operation operation) throws VisitorException {
			int arity = info.getArity();
			Operation.Operator op = operation.getOperator();
			if (arity == op.getArity()) {
				Expression operhands [] = new Expression [arity];
				for (int i = 0; i< arity; i++) {
					operhands[i] = info.children.get(i).ownedExp;
				}
				switch (op) {
				case EQ:
					if ((operhands[1] instanceof Variable) && !(operhands[0] instanceof Variable)) {
						Expression temp = operhands[1];
						operhands[1] = operhands[0];
						operhands[0] = temp;
						altered = true;
					} 
					if ((operhands[0] instanceof Variable) && (operhands[1] instanceof Constant)) {
						info.knownVars.putIfAbsent((Variable) operhands[0], (Expression) operhands[1]);
						if (info.children.get(0).ownedExp instanceof Variable) {
							info.children.get(0).noReplaceVars.add((Variable) operhands[0]);
						} else {
							info.children.get(1).noReplaceVars.add((Variable) operhands[0]);
						}
					}
					if ((operhands[0] instanceof Constant) && (operhands[1] instanceof Constant)) {
						//Check if equal
					}
					
					
				}
					info.ownedExp = new Operation(op, operhands[0], operhands[1]);
			} else {
				//arity does not match
			}
			
			
			postVisit((Expression) operation);
		}

		public void postVisit(RealConstant realConstant) throws VisitorException {
			postVisit((Constant) realConstant);
		}

		public void postVisit(RealVariable realVariable) throws VisitorException {
			postVisit((Variable) realVariable);
		}

		public void postVisit(StringConstant stringConstant) throws VisitorException {
			postVisit((Constant) stringConstant);
		}

		public void postVisit(StringVariable stringVariable) throws VisitorException {
			postVisit((Variable) stringVariable);
		}

		public void postVisit(Variable variable) throws VisitorException {
			Expression exp = info.knownVars.get(variable);
			if (exp != null) {
				if (!(exp instanceof Constant)) {
					exp = variable;
				}
			} else {
				exp =  variable;
			}
			info.ownedExp = exp;
			
			postVisit((Expression) variable);
		}
	}
	
	/*public static void main(String args[]) {
		IntVariable x = new IntVariable("x", 0, 99);
		IntVariable y = new IntVariable("y", 0, 99);
		IntVariable z = new IntVariable("z", 0, 99);
		IntConstant c = new IntConstant(1);
		IntConstant c10 = new IntConstant(10);
		IntConstant c9 = new IntConstant(9);
		IntConstant c3 = new IntConstant(3);
		Operation o1 = new Operation(Operation.Operator.EQ, x, c); // o1 : x = 1
		Operation o2 = new Operation(Operation.Operator.ADD, x, y); // o2 : (x + y)
		//Operation o2 = new Operation(Operation.Operator.ADD, c, c9); // o2 : (x + y)
		Operation o3 = new Operation(Operation.Operator.EQ, o2, c10); // o3 : x+y = 10
		Operation o4 = new Operation(Operation.Operator.AND, o1, o3); // o4 : x = 1 && (x+y) = 10 
		
		
		ConstantPropagation simplify = new ConstantPropagation(o4);
		
		
		
	}*/
	
	public static void loopOp (Operation op) {
		
	}

	/*public static Operation simplifyOp(Operation origin) {
		ConstantPropagation simplify = new ConstantPropagation(origin);
		return (Operation) simplify.binTree.ownedExp;
	}*/
}