package org.tzi.mvm;

import java.util.ArrayList;
import java.util.List;

import org.tzi.use.uml.mm.MAssociation;

public class AssocWizard {
	private String name;
	private String state ;
	private List<LinkWizard> lLinks;
	private MAssociation assocModel;

	public AssocWizard() {
		super();
		this.name = "";
		this.state = "";
		ArrayList<LinkWizard> lLinks = new ArrayList<LinkWizard>();
		this.lLinks = lLinks;
		this.assocModel= null;
	}

	public AssocWizard(String name, String state, List<LinkWizard> lLinks, MAssociation assocModel) {
		super();
		this.name = name;
		this.state = state;
		this.lLinks = lLinks;
		this.assocModel = assocModel;
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
	public MAssociation getassocModel() {
		return assocModel;
	}

	public void setassocModel(MAssociation assocModel) {
		this.assocModel = assocModel;
	}	
}
