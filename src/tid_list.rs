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
			// If the last item is the same as the new item, ignore it
			Some(last_tid) if last_tid.0 == tid.0 => (),
			// If empty or different last item, add it
			_ => self.tids.push(tid)
		}
	}
	
	pub fn get_slice(&mut self) -> &mut[types::Tid] {
		&mut self.tids[..]
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn test_no_duplicates() {
		let mut list = super::TidList::new();
		
		assert!(list.tids.is_empty());
		
		for i in 0..10 {
			list.push(super::types::Tid(i));
			assert!(list.tids.last().unwrap().0 == i);
			assert!(list.tids.len() == (i + 1) as usize);
		}
	}
}
