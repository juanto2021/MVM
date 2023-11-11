package org.tzi.mvm;

import java.util.ArrayList;
import java.util.List;

public class AssocWizard {
	private String name;
	private String state ;
	private List<LinkWizard> lLinks;

	public AssocWizard() {
		super();
		this.name = "";
		this.state = "";
		ArrayList<LinkWizard> lLinks = new ArrayList<LinkWizard>();
		this.lLinks = lLinks;
	}

	public AssocWizard(String name, String state, List<LinkWizard> lLinks) {
		super();
		this.name = name;
		this.state = state;
		this.lLinks = lLinks;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getState() {
		return state;
	}

	public void setState(String state) {
		this.state = state;
	}

	public List<LinkWizard> getlLinks() {
		return lLinks;
	}

	public void setlLinks(List<LinkWizard> lLinks) {
		this.lLinks = lLinks;
	}
}
