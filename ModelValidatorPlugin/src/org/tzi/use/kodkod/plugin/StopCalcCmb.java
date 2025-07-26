package org.tzi.use.kodkod.plugin;

import java.awt.Cursor;
import java.io.PrintWriter;
import java.io.StringWriter;

import javax.swing.JOptionPane;

import org.apache.commons.configuration.Configuration;
import org.apache.commons.configuration.ConfigurationException;
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.UseKodkodModelValidator;
import org.tzi.use.kodkod.plugin.gui.ModelValidatorConfigurationWindowMVM;
import org.tzi.use.main.Session;
import org.tzi.use.runtime.gui.IPluginAction;
import org.tzi.use.runtime.gui.IPluginActionDelegate;
import org.tzi.use.uml.mm.MModel;
import org.tzi.use.uml.sys.MSystem;

public class StopCalcCmb implements IPluginActionDelegate {


	@Override
	public void performAction(IPluginAction pluginAction) {

		if(!pluginAction.getSession().hasSystem()){
			JOptionPane.showMessageDialog(pluginAction.getParent(),
					"No model present.", "No Model", JOptionPane.ERROR_MESSAGE);
			return;
		}
		Session session = pluginAction.getSession();

		MSystem mSystem= session.system();
		MModel mModel = mSystem.model();

		PluginModelFactory.INSTANCE.registerForSession(session);

		KodkodValidateCmd cmd = new KodkodValidateCmd();
		cmd.session=session;
		cmd.mSystem = mSystem;
		cmd.mModel = mModel;
		cmd.useShell = null;

		// Activamos hourglass

		UseKodkodModelValidator uk = MainWindow.instance().getKodKod();
		if (uk!=null) {
			MainWindow.instance().setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
			uk.stopThreadCmb();
			MainWindow.instance().setCursor(Cursor.getDefaultCursor());
		}else {
			JOptionPane.showMessageDialog(pluginAction.getParent(),
					"No calculations running.", "Search for combinations", JOptionPane.ERROR_MESSAGE);
		}
	}
}
