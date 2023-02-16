package org.tzi.mvm;


import java.util.Set;
import java.util.TreeSet;
/**
 * Class representing a combination of invariants
 * @author Juanto
 *
 */
public class Combination {	

//	private static final long serialVersionUID = 1L;
	/**
	 * Invariants that make up the combination
	 */
	//	private Set<String> invariants= new HashSet<String>();
	private Set<String> invariants= new TreeSet<String>();
	private static int contador=0;
	/**
	 * Constructor with Set of invariants
	 * @param invariants that make up the combination
	 */
	public Combination(Set<String> invariants) {
		super();
		this.invariants = invariants;
	}
	/**
	 * Constructor with array of invariants
	 * @param arrInvs invariants that make up the combination
	 */
	public Combination(String[] arrInvs) {
		super();
		for(int nInv = 0;nInv<arrInvs.length;nInv++) {
			invariants.add(arrInvs[nInv]);
		}
	}	
	/**
	 * Constructor for combination without invariants
	 */
	public Combination() {
		super();
	}
	/**
	 * Returns Set of invariants
	 * @return Set of invariants
	 */
	public Set<String> getInvariants() {
		return invariants;
	}
	/**
	 * Initialize Set of invariants
	 * @param invariants that make up the combination
	 */
	public void setInvariants(Set<String> invariants) {
		//		this.invariants = invariants;
		this.invariants.addAll(invariants);
	}
	/**
	 * Analyze if a combination is included in the current combination (this)
	 * @param cmb that should be contained in the current combination
	 * @return true/false if a combination is included in the current combination (this)
	 */
	public boolean containsCmb(Combination cmb) {
		if (this.getInvariants().containsAll(cmb.getInvariants())) {
			return true;
		}
		return false;
	}
	/**
	 * Analyze if the current combination (this) is included in a combination
	 * @param cmb What should the current combination contain?
	 * @return true/false if the current combination (this) is included in a combination
	 */
	public boolean cmbContainedIn(Combination cmb) {
		if (cmb.getInvariants().containsAll(this.getInvariants())) {
			return true;
		}
		return false;
	}
	/**
	 * Returns number of invariants of the combination
	 * @return number of invariants of the combination
	 */
	public int sizeIn() {
		return getInvariants().size();
	}
	/**
	 * Sorts the invariants within the current combination
	 * @return ordered combination
	 */
	public Combination sortCombination() {
		TreeSet<String> treeSet = new TreeSet<String>(getInvariants());	
		Combination cmbCombination= new Combination(treeSet);
		return cmbCombination;
	}

	public void addInv(String inv) {
		this.invariants.add(inv);
		return;
	}
	/**
	 * Returns a sum combination of 2 others
	 * @param cmb1 combination to join
	 * @param cmb2 combination to join
	 * @return combination of combinations 1 and 2
	 */
	public static Combination addInvs(Combination cmb1, Combination cmb2) {
		Combination cmbRes = new Combination();
		cmbRes.invariants.addAll(cmb1.invariants);
		cmbRes.invariants.addAll(cmb2.invariants);
		return cmbRes;
	}
	/**
	 * Returns a combination with the invariants of the first combination that are not in the second
	 * @param cmb1 first combination 
	 * @param cmb2 second combination
	 * @return combinations of the first that are not in the second
	 */
	public static Combination subInvs(Combination cmb1, Combination cmb2) {
		Combination cmbRes = new Combination();
		cmbRes.invariants.addAll(cmb1.invariants);
		cmbRes.invariants.removeAll(cmb2.invariants);
		return cmbRes;
	}
	/**
	 * Returns combination with the common invariants of 2 combinations
	 * @param cmb1 first combination 
	 * @param cmb2 second combination
	 * @return combinations that are in both combinations
	 */
	public static Combination idenInvs(Combination cmb1, Combination cmb2) {
		Combination cmbRes = new Combination();
		cmbRes.invariants.addAll(cmb1.invariants);
		cmbRes.invariants.retainAll(cmb2.invariants);
		return cmbRes;
	}
	/**
	 * Return combination with invariants that are not in both combinations simultaneously
	 * @param cmb1 first combination
	 * @param cmb2 second combination
	 * @return combinations that are not in both combinations
	 */
	public static Combination difInvs(Combination cmb1, Combination cmb2) {
		Combination cmbDif = new Combination();
		cmbDif.invariants.addAll(cmb1.invariants);
		cmbDif.invariants.retainAll(cmb2.invariants);		

		// Suma
		Combination cmbRes = new Combination();
		cmbRes.invariants.addAll(cmb1.invariants);
		cmbRes.invariants.addAll(cmb2.invariants);
		// Diferencia
		cmbRes.invariants.removeAll(cmbDif.invariants);
		return cmbRes;
	}	
	/**
	 * Classic ToString
	 */
	@Override
	public String toString() {
		String str = invariants.toString().replaceAll(", ", "-");
		return "Combination [invariants=" + str + "]";
	}
	public String getKey() {
		contador++;
//		System.out.println(contador);
		String str = invariants.toString().replaceAll(", ", "-");
		return "Combination [invariants=" + str + "]";
	}
	public String strStr() {
		String res="";
		for (String cmb : invariants) {
			if (res!="") {
				res+="-";
			}
			res+=cmb;
		}		
		return res;
	}
}
