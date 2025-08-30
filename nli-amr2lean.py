import shutil
from propbank_interface import PropbankCatalogue
from amr2lean2 import AMR2LeanTranslator
from amr_toolbox.AMRLoader import AMRLoader
import pandas as pd 

if __name__ == '__main__':
	base_dir = '/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/'
	hypothesis_amrs_path = base_dir + 'data_all_amr_nli_final/sick.dev.txt.amrhypothesis'
	premise_amrs_path = base_dir + 'data_all_amr_nli_final/sick.dev.txt.amrpremise'

	amr_loader = AMRLoader('')

	hypo_amrs = amr_loader.read_amrs(hypothesis_amrs_path, keep_indentation=True)
	prem_amrs = amr_loader.read_amrs(premise_amrs_path, keep_indentation=True)
	hypo_amrs_dict = {amr_dict['id']: amr_dict for amr_dict in hypo_amrs}
	prem_amrs_dict = {amr_dict['id']: amr_dict for amr_dict in prem_amrs}


	hyp_prm_csv_path = base_dir + 'data_all_amr_nli_final/sick_dev.csv'

	hypo_prem_pairing = pd.read_csv(hyp_prm_csv_path)

	propbank_dir = '/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/propbank-frames/frames/'
	import_semantic_gdt = False

	pb_catalog = PropbankCatalogue(propbank_dir)
	
	amr_gadgets_file = './AMRGadgets.lean'
	lean_saving_dir = base_dir + 'nli_amr2lean/'

	# if choose to have amr gadgets module imported, copy the gadget file over to the lean code base
	if import_semantic_gdt:
		shutil.copy(amr_gadgets_file, lean_saving_dir)


	total_amrs = 0
	for row in hypo_prem_pairing.itertuples():
		prem_id = str(row.premise)
		hypo_id = str(row.hypothesis)

		if row.entailment_judgment == 'NEUTRAL':
			continue		
		with open(lean_saving_dir + 'sick-dev'+f'-{str(row.pair_ID)}.lean', 'w') as f:
			f.write(f'-- {str(row.pair_ID)} --\n')
			t1 = AMR2LeanTranslator(propbank_catelog=pb_catalog, import_semantic_gadgets=import_semantic_gdt)

			amr1 = prem_amrs_dict[prem_id]['amr']
			amr2 = hypo_amrs_dict[hypo_id]['amr']

			prem_leancode = t1.translate(amr1)
			# new_leancode = reorder_choice_blocks(leancode)
			t2 = AMR2LeanTranslator(propbank_catelog=pb_catalog, import_semantic_gadgets=import_semantic_gdt)
			
			hypo_leancode = t2.translate(amr2)

			t1.M.update_inventory(t2.M.roles_inventory)

			extra_axiom_insertion_comment = '\n'+'-- insert language understanding or common sense knowledge here\n' + '-- knowledge axioms -- \n'+'\n'

			final_code = t1.M.render() + extra_axiom_insertion_comment + '\n\n' + t2.M.single_theorem_render(row.entailment_judgment == 'CONTRADICTION')

			f.write(final_code)
			f.write('\n\n')
			total_amrs += 1

	print('total_amrs: ', total_amrs)


