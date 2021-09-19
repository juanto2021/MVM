package org.tzi.use.kodkod.plugin;

import java.util.List;

import org.tzi.kodkod.model.iface.IInvariant;

public class ResValidation {
	public List<IInvariant> lInvs;
	public String outcome;
	
	public ResValidation(List<IInvariant> lInvs, String strOutcome) {
		super();
		this.lInvs = lInvs;
		this.outcome = strOutcome;
	}

	public List<IInvariant> getlInvs() {
		return lInvs;
	}

	public void setlInvs(List<IInvariant> lInvs) {
		this.lInvs = lInvs;
	}

	public String getOutcome() {
		return outcome;
	}

	public void setOutcome(String strOutcome) {
		this.outcome = strOutcome;
	}
}