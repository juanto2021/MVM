package org.tzi.mvm;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.tzi.use.uml.ocl.expr.Expression;

public class classes_inv {
	String name;
	List<String> inv_attr;
	
	public classes_inv() {
		inv_attr = new ArrayList<String>();
	}
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	public List<String> getInv_attr() {
		return inv_attr;
	}
	public void setInv_attr(List<String> inv_attr) {
		this.inv_attr = inv_attr;
	}
	
}
