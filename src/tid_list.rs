use crate::types;

pub struct TidList {
	tids: Vec<types::Tid>
}

impl TidList {
	pub fn new() -> TidList {
		TidList { tids: Vec::new() }
	}
	
	pub fn push(&mut self, tid: types::Tid) {
		match self.tids.last() {
			Some(last_tid) => {
				if last_tid.0 != tid.0 {
					self.tids.push(tid);
				}
			},
			_ => ()
		}
	}
	
	pub fn get_slice(&mut self) -> &mut[types::Tid] {
		&mut self.tids[..]
	}
}
