package org.tzi.use.kodkod.plugin;

import java.awt.Cursor;
import java.io.PrintWriter;
import java.io.StringWriter;

import javax.swing.JOptionPane;

import org.apache.commons.configuration.Configuration;
import org.apache.commons.configuration.ConfigurationException;
import org.tzi.kodkod.helper.LogMessages;
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.UseKodkodModelValidator;
import org.tzi.use.kodkod.plugin.gui.ModelValidatorConfigurationWindowMVM;
import org.tzi.use.main.Session;
import org.tzi.use.runtime.gui.IPluginAction;
import org.tzi.use.runtime.gui.IPluginActionDelegate;
import org.tzi.use.uml.mm.MModel;
import org.tzi.use.uml.sys.MSystem;

/**
 * Action-Class to extend the toolbar with a button to call the model validator
 * with a configuration file.
 * Using analysis_OCL method to find MSS
 * @author Juanto
 * 
 */
public class KodkodValidateMVMActionG  implements IPluginActionDelegate {

	@Override
	public void performAction(IPluginAction pluginAction) {
		// Llama al validador Alternativo

		if(!pluginAction.getSession().hasSystem()){
			JOptionPane.showMessageDialog(pluginAction.getParent(),
					"No model present.", "No Model", JOptionPane.ERROR_MESSAGE);
			return;
		}
		Session session = pluginAction.getSession();

		MSystem mSystem= session.system();
		MModel mModel = mSystem.model();
		//try {
		PluginModelFactory.INSTANCE.registerForSession(session);
		//} catch (Exception e) {
		//
		//}

		//		PluginModelFactory.INSTANCE.registerForSession(session);// Provis
		IModel model = PluginModelFactory.INSTANCE.getModel(mModel);// provis

		KodkodValidateCmd cmd = new KodkodValidateCmd();
		cmd.session=session;
		cmd.mSystem = mSystem;
		cmd.mModel = mModel;
		cmd.useShell = null;

		ModelValidatorConfigurationWindowMVM modelValidatorConfigurationWindow = 
				new ModelValidatorConfigurationWindowMVM(MainWindow.instance(), model, mModel.filename());

		Configuration config = modelValidatorConfigurationWindow.getChosenConfiguration();

		StringWriter errorBuffer = new StringWriter();
		try {
			cmd.configureModel(config, new PrintWriter(errorBuffer, true));
		} catch (ConfigurationException e) {
			MainWindow.instance().setCursor(Cursor.getDefaultCursor());
			e.printStackTrace();
		}
		// Activamos hourglass
		MainWindow.instance().setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
		UseKodkodModelValidator uk = new UseKodkodModelValidator(session);
//		MainWindow.instance().v
		MainWindow.instance().setKodKod(uk);
		String tipoSearchMSS = "G";
		uk.validateVariable(model, mModel, session, tipoSearchMSS);
		// Desactivamos hourglass
		MainWindow.instance().setCursor(Cursor.getDefaultCursor());

	}

}
