package org.tzi.use.kodkod.plugin;

import java.awt.Cursor;
import java.io.PrintWriter;
import java.io.StringWriter;

import javax.swing.JOptionPane;
import javax.swing.SwingUtilities;

import org.apache.commons.configuration.Configuration;
import org.apache.commons.configuration.ConfigurationException;
import org.tzi.kodkod.EventThreads;
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.UseKodkodModelValidator;
import org.tzi.use.kodkod.plugin.gui.ModelValidatorConfigurationWindowMVM;
import org.tzi.use.kodkod.plugin.gui.ValidatorMVMDialogSimple;
import org.tzi.use.main.Session;
import org.tzi.use.runtime.gui.IPluginAction;
import org.tzi.use.runtime.gui.IPluginActionDelegate;
import org.tzi.use.uml.mm.MModel;
import org.tzi.use.uml.sys.MSystem;

/**
 * Action-Class to extend the toolbar with a button to call the model validator
 * with a configuration file.
 * Using bruteForceMethod method
 * @author Juanto
 * 
 */
public class KodkodValidateMVMActionL  implements IPluginActionDelegate {

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

		IModel model = PluginModelFactory.INSTANCE.getModel(mModel);

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

		UseKodkodModelValidator uk = MainWindow.instance().getKodKod();
		if (uk==null) {
			uk = new UseKodkodModelValidator(session);
		}
		EventThreads threadGreedy = uk.getThreadGreedy();

		final UseKodkodModelValidator uk2 = uk;

		boolean calON=uk.getCalON();
		if (calON || threadGreedy !=null) {
			JOptionPane.showMessageDialog(pluginAction.getParent(),
					"A combination search already exists. Stop it first.", "Greedy calculation launches", JOptionPane.ERROR_MESSAGE);
		}else {
			// We activate the hourglass
			MainWindow.instance().setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
			MainWindow.instance().statusBar().showMessage("Searching for combinations using Brute force1...");

			MainWindow.instance().enableAction("ValidationMVMG", false);
			MainWindow.instance().enableAction("ValidationMVMB", false);
			MainWindow.instance().enableAction("StopCalcCmb", true);
			MainWindow.instance().enableAction("ShowDiaCmb", false);
			MainWindow.instance().statusBar().validate();

			SwingUtilities.invokeLater(() -> {		

				MainWindow.instance().statusBar().showMessage("Searching for combinations using Brute force...");
			});

			SwingUtilities.invokeLater(() -> {
				MainWindow.instance().setKodKod(uk2);

				// If the dialogue exists, we delete it.
				ValidatorMVMDialogSimple dia = MainWindow.instance().getValidatorDialog();

				if (dia!=null) {
					dia.dispose();
					MainWindow.instance().setValidatorDialog(null);
				}

				String tipoSearchMSS = "L";
				uk2.validateVariable(model, mModel, session, tipoSearchMSS);
				// We deactivate the hourglass		
				MainWindow.instance().setCursor(Cursor.getDefaultCursor());
			});
		}
	}

}
