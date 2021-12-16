use crate::types;
use crate::tid_list;

use std::io::BufRead;
use std::collections::HashMap;

#[derive(std::cmp::PartialEq, std::cmp::Eq, Hash, Copy, Clone, Debug)]
pub struct InputEdgeLabel(i16);
#[derive(std::cmp::PartialEq, std::cmp::Eq, Hash, Copy, Clone, Debug)]
pub struct InputNodeLabel(i16);
#[derive(std::cmp::PartialEq, Debug)]
pub struct InputNodeId(i16);

type CombinedInputLabel = (InputNodeLabel, InputEdgeLabel, InputNodeLabel);

pub struct DatabaseTreeEdge {
	pub edgelabel: types::EdgeLabel,
	pub tonode: types::NodeId,
}

pub struct DatabaseTreeNode {
	pub nodelabel: types::NodeLabel,
	pub edges: Vec<DatabaseTreeEdge>,
	pub mark: types::PatternMask, // Might not want these two here
	pub startmark: types::PatternMask,
}

impl DatabaseTreeNode {
	pub fn new(nodelabel: types::NodeLabel , edges: Vec<DatabaseTreeEdge>) -> DatabaseTreeNode {
		DatabaseTreeNode {
			nodelabel,
			edges,
			mark: types::PatternMask(1),
			startmark: types::PatternMask(1)
		}
	}
}

pub struct DatabaseTree {
	pub tid: types::Tid,
	pub nodes: Vec<DatabaseTreeNode>,
}

impl DatabaseTree {
	pub fn new(tid: types::Tid) -> DatabaseTree {
		DatabaseTree { tid, nodes: Vec::new() }
	}
}

pub struct DatabaseNodeLabel {
	pub input_node_label: InputNodeLabel,
	pub frequency: types::Frequency,
	pub occurrence_count: types::Frequency,
	pub frequent_edge_labels: Vec<types::EdgeLabel>,
}

pub struct DatabaseEdgeLabel {
	pub input_edge_label: InputEdgeLabel,
	pub to_node_label: types::NodeLabel,
	pub from_node_label: types::NodeLabel,
	pub edge_label: types::EdgeLabel,
	pub frequency: types::Frequency,
	pub occurrence_count: types::Frequency,
	pub tid_list: tid_list::TidList,
}

// Used as an intermediate form before being converted to either a DatabaseNodeLabel or DatabaseEdge
#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
struct DatabaseLabelCounts {
	frequency: types::Frequency,
	occurrence_count: types::Frequency,
	last_tid: usize,
}

pub struct Database {
	pub trees: Vec<DatabaseTree>,
	pub node_labels: Vec<DatabaseNodeLabel>,
	pub edge_labels: Vec<DatabaseEdgeLabel>,
	pub largest_n_nodes: u32,
	pub largest_n_edges: u32,
	pub edge_labels_indexes: Vec<types::EdgeLabel>,
}

#[derive(Debug)]
pub enum DatabaseError {
	IncompleteGraphCommand(usize),
	IncompleteNodeCommand(usize),
	IncompleteEdgeCommand(usize),
	UnknownCommand(usize, String),
	InvalidFirstLine,
	InvalidTid(usize, types::Tid, usize),
	InvalidNodeId(usize, InputNodeId, usize),
	UnknownNodeId(usize, InputNodeId, usize),
	ParseError(usize, std::num::ParseIntError),
	IOError(std::io::Error),
}

impl std::fmt::Display for DatabaseError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			Self::IncompleteGraphCommand(line_no) =>
				write!(f, "line {}: Incomplete graph, requires \"t # [id]\"", line_no),
			Self::IncompleteNodeCommand(line_no) =>
				write!(f, "line {}: Incomplete node, requires \"v [id] [label]\"", line_no),
			Self::IncompleteEdgeCommand(line_no) =>
				write!(f, "line {}: Incomplete edge, requires \"e [nodeid1] [nodeid2] [label]\"", line_no),
			Self::UnknownCommand(line_no, tok) =>
				write!(f, "line {}: Unknown command \"{}\", expected t, v, or e", line_no, tok),
			Self::InvalidTid(line_no, given, expected) =>
				write!(f, "line {}: Expected graph id {}, was given {} instead. (graph ids should be given in ascending order from 0)", line_no, expected, given.0),
			Self::InvalidNodeId(line_no, given, expected) =>
				write!(f, "line {}: Expected node id {}, was given {} instead. (node ids should be given in ascending order from 0)", line_no, expected, given.0),
			Self::UnknownNodeId(line_no, given, maximum) =>
				write!(f, "line {}: Id {} out of range, maximum vertex id is {}", line_no, given.0, maximum),
			Self::InvalidFirstLine =>
				write!(f, "First line should be \"t # 0\""),
			Self::ParseError(line_no, err) =>
				write!(f, "line {}: {}", line_no, err),
			Self::IOError(err) =>
				write!(f, "{}", err),
		}
	}
}

impl std::convert::From<std::io::Error> for DatabaseError {
	fn from(err: std::io::Error) -> Self {
		Self::IOError(err)
	}
}

#[derive(std::cmp::PartialEq, Debug)]
enum Command {
	Graph(types::Tid),
	Node(InputNodeId, InputNodeLabel),
	Edge(InputNodeId, InputNodeId, InputEdgeLabel),
}

#[derive(std::cmp::PartialEq, Debug)]
struct RawInputNode {
	label: InputNodeLabel,
}

#[derive(std::cmp::PartialEq, Debug)]
struct RawInputEdge {
	from: InputNodeId,
	to:   InputNodeId,
	label: InputEdgeLabel,
}

#[derive(std::cmp::PartialEq, Debug)]
struct RawInputGraph {
	nodes: Vec<RawInputNode>,
	edges: Vec<RawInputEdge>,
}

impl Database {
	pub fn read(filename: &str) -> Result<Database, DatabaseError> {
		let reader = std::io::BufReader::new(std::fs::File::open(filename)?);
		
		let mut trees = Self::parse_input(reader)?;
		
		let (node_labels, edge_labels) = Self::count_labels(&trees);
		
		Ok(Database {
			trees: Vec::new(),
			node_labels: Vec::new(),
			edge_labels: Vec::new(),
			largest_n_nodes: 0,
			largest_n_edges: 0,
			edge_labels_indexes: Vec::new(),
		})
	}
	
	fn parse_input<R: std::io::Read>(reader: std::io::BufReader<R>)
		-> Result<Vec<RawInputGraph>, DatabaseError> {
		let mut trees = Vec::new();
		
		for (line_no, line) in reader.lines().enumerate().map(|(n,l)| (n+1,l)) {
			match Self::read_command((line_no, &line?))? {
				Some(Command::Graph(tid)) => {
					if tid.0 as usize != trees.len() {
						return Err(DatabaseError::InvalidTid(line_no, tid, trees.len()));
					}
					
					trees.push(RawInputGraph { nodes: Vec::new(), edges: Vec::new() } );
				},
				Some(Command::Node(id, label)) => {
					let nodes =
						&mut trees.last_mut().ok_or(DatabaseError::InvalidFirstLine)?.nodes;
					
					if id.0 as usize != nodes.len() {
						return Err(DatabaseError::InvalidNodeId(line_no, id, nodes.len()));
					}
					
					nodes.push(RawInputNode { label });
				},
				Some(Command::Edge(id1, id2, label)) => {
					let last_graph = &mut trees.last_mut().ok_or(DatabaseError::InvalidFirstLine)?;
					
					let n_verts = last_graph.nodes.len();
					
					if id1.0 as usize >= n_verts {
						return Err(DatabaseError::UnknownNodeId(line_no, id1, n_verts));
					}
					if id2.0 as usize >= n_verts {
						return Err(DatabaseError::UnknownNodeId(line_no, id2, n_verts));
					}
					
					last_graph.edges.push(RawInputEdge { from: id1, to: id2, label });
				},
				None => ()
			}
		}
		
		Ok(trees)
	}
	
	fn count_label<K: std::hash::Hash + Eq>(labels: &mut HashMap<K, DatabaseLabelCounts>, key: K, tid: usize) {
		let label = labels.entry(key).or_insert(DatabaseLabelCounts {
			frequency: 1,
			occurrence_count: 0,
			last_tid: tid,
		});
		label.occurrence_count += 1;
		if label.last_tid != tid {
			label.frequency += 1;
			label.last_tid = tid;
		}
	}
	
	fn count_labels(trees: &[RawInputGraph]) -> (HashMap<InputNodeLabel, DatabaseLabelCounts>,
		HashMap<CombinedInputLabel, DatabaseLabelCounts>) {
		let mut node_labels = HashMap::new();
		let mut edge_labels = HashMap::new();
		
		for (tid, tree) in trees.iter().enumerate() {
			for node in &tree.nodes {
				Self::count_label(&mut node_labels, node.label, tid);
			}
			
			for edge in &tree.edges {
				let node_label1 = tree.nodes[edge.from.0 as usize].label;
				let node_label2 = tree.nodes[edge.to  .0 as usize].label;
				let (large, small) = if node_label1.0 > node_label2.0 
						{ (node_label1, node_label2) }
					else
						{ (node_label2, node_label1) };
				
				Self::count_label(&mut edge_labels, (large, edge.label, small), tid);
			}
		}
		
		(node_labels, edge_labels)
	}
	
	// Returns the next token from iter. Returns err if there is no token, or a ParseIntError
	// if parsing fails.
	fn parse_token<T>(iter: &mut std::str::SplitWhitespace, line_no: usize, err: DatabaseError)
		-> Result<T, DatabaseError>
		where T: std::str::FromStr<Err = std::num::ParseIntError> {
		iter.next()
		    .ok_or(err)?
		    .parse()
		    .map_err(|e| DatabaseError::ParseError(line_no, e))
	}
	
	// Returns an optional command (no command if the line is empty) parsed
	// from line.
	fn read_command((line_no, line): (usize, &str)) -> Result<Option<Command>, DatabaseError> {
		let mut token_iterator = line.split_whitespace();
		
		match token_iterator.next() {
			Some("t") => {
				// Errors here would be useless, so just skip the next token
				token_iterator.next();
				
				let tid = Self::parse_token(&mut token_iterator,
					line_no, DatabaseError::IncompleteGraphCommand(line_no))?;
				
				Ok(Some(Command::Graph(
					types::Tid(tid)
				)))
			},
			Some("v") => {
				let id = Self::parse_token(&mut token_iterator,
					line_no, DatabaseError::IncompleteNodeCommand(line_no))?;
				
				let label = Self::parse_token(&mut token_iterator,
					line_no, DatabaseError::IncompleteNodeCommand(line_no))?;
				
				Ok(Some(Command::Node(
					InputNodeId(id),
					InputNodeLabel(label)
				)))
			},
			Some("e") => {
				let nodeid1 = Self::parse_token(&mut token_iterator,
					line_no, DatabaseError::IncompleteEdgeCommand(line_no))?;
				
				let nodeid2 = Self::parse_token(&mut token_iterator,
					line_no, DatabaseError::IncompleteEdgeCommand(line_no))?;
				
				let label = Self::parse_token(&mut token_iterator,
					line_no, DatabaseError::IncompleteEdgeCommand(line_no))?;
				
				Ok(Some(Command::Edge(
					InputNodeId(nodeid1),
					InputNodeId(nodeid2),
					InputEdgeLabel(label)
				)))
			},
			Some(tok) => Err(DatabaseError::UnknownCommand(line_no, tok.to_owned())),
			None => Ok(None),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	
	#[test]
	fn test_valid_commands() {
		let result = Database::read_command((0, "t # 5"));
		assert_eq!(result.unwrap(), Some(Command::Graph(types::Tid(5))));
		
		let result = Database::read_command((0, "v 5 6"));
		assert_eq!(result.unwrap(), Some(Command::Node(InputNodeId(5), InputNodeLabel(6))));
		
		let result = Database::read_command((0, "e 1 0 2"));
		assert_eq!(result.unwrap(), Some(Command::Edge(
			InputNodeId(1), InputNodeId(0), InputEdgeLabel(2)
		)));
		
		let result = Database::read_command((0, ""));
		assert!(result.unwrap().is_none());
	}
	
	#[test]
	fn test_unknown_command() {
		let err = Database::read_command((10, "w 4 50")).unwrap_err();
		assert!(matches!(&err, DatabaseError::UnknownCommand(line_no, tok)
			if line_no == &10 && tok == "w"
		));
		
		let msg = err.to_string();
		assert_eq!(msg, "line 10: Unknown command \"w\", expected t, v, or e");
	}
	
	#[test]
	fn test_incomplete_commands() {
		// Incomplete graph commands
		let err = Database::read_command((15, "t")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteGraphCommand(line_no)
			if line_no == &15
		));
		
		let err = Database::read_command((18, "t #")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteGraphCommand(line_no)
			if line_no == &18
		));
		
		let msg = err.to_string();
		assert_eq!(msg, "line 18: Incomplete graph, requires \"t # [id]\"");
		
		// Incomplete node commands
		let err = Database::read_command((23, "v")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteNodeCommand(line_no)
			if line_no == &23
		));
		
		let err = Database::read_command((27, "v 0")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteNodeCommand(line_no)
			if line_no == &27
		));
		
		let msg = err.to_string();
		assert_eq!(msg, "line 27: Incomplete node, requires \"v [id] [label]\"");
		
		// Incomplete edge commands
		let err = Database::read_command((34, "e")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteEdgeCommand(line_no)
			if line_no == &34
		));
		
		let err = Database::read_command((36, "e 0")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteEdgeCommand(line_no)
			if line_no == &36
		));
		
		let err = Database::read_command((39, "e 0 12")).unwrap_err();
		assert!(matches!(&err, DatabaseError::IncompleteEdgeCommand(line_no)
			if line_no == &39
		));
		
		let msg = err.to_string();
		assert_eq!(msg, "line 39: Incomplete edge, requires \"e [nodeid1] [nodeid2] [label]\"");
	}
	
	#[test]
	fn test_parse_errors() {
		let err = Database::read_command((1, "t # thing")).unwrap_err();
		assert!(matches!(&err, DatabaseError::ParseError(line_no, _)
			if line_no == &1
		));
		
		let err = Database::read_command((5, "v sauce")).unwrap_err();
		assert!(matches!(&err, DatabaseError::ParseError(line_no, _)
			if line_no == &5
		));
		
		let err = Database::read_command((12, "v 45 x")).unwrap_err();
		assert!(matches!(&err, DatabaseError::ParseError(line_no, _)
			if line_no == &12
		));
		
		let err = Database::read_command((34, "e $$&&@*#&*($@")).unwrap_err();
		assert!(matches!(&err, DatabaseError::ParseError(line_no, _)
			if line_no == &34
		));
		
		let err = Database::read_command((54, "e 45 *")).unwrap_err();
		assert!(matches!(&err, DatabaseError::ParseError(line_no, _)
			if line_no == &54
		));
		
		let err = Database::read_command((154, "e 0 0 ()")).unwrap_err();
		assert!(matches!(&err, DatabaseError::ParseError(line_no, _)
			if line_no == &154
		));
	}
	
	#[test]
	fn test_parse_input_errors() {
		use std::io::BufReader;
		use DatabaseError::*;
		
		let err = Database::parse_input(BufReader::new("v 0 0".as_bytes())).unwrap_err();
		assert!(matches!(&err, InvalidFirstLine));
		
		let err = Database::parse_input(BufReader::new("e 0 0 0".as_bytes())).unwrap_err();
		assert!(matches!(&err, InvalidFirstLine));
		
		let err = Database::parse_input(BufReader::new("t".as_bytes())).unwrap_err();
		assert!(matches!(&err, IncompleteGraphCommand(line_no)
			if line_no == &1
		));
		
		let s = "t # 0\n\
		         v 1 15\n\
		         v 3 4\n";
		let err = Database::parse_input(BufReader::new(s.as_bytes())).unwrap_err();		
		assert!(matches!(&err, InvalidNodeId(line_no, given, size)
			if line_no == &2 && given.0 == 1 && size == &0
		));
		
		let s = "t # 0\n\
		         v 0 15\n\
		         v 1 4\n\
		         e 0 2 5";
		let err = Database::parse_input(BufReader::new(s.as_bytes())).unwrap_err();		
		assert!(matches!(&err, UnknownNodeId(line_no, given, size)
			if line_no == &4 && given.0 == 2 && size == &2
		));
		
		let s = "t # 0\n\
		         v 0 15\n\
		         v 1 4\n\
		         t 0 7";
		let err = Database::parse_input(BufReader::new(s.as_bytes())).unwrap_err();		
		assert!(matches!(&err, InvalidTid(line_no, given, size)
			if line_no == &4 && given.0 == 7 && size == &1
		));
	}
	
	#[test]
	fn test_parse_input() {
		use std::io::BufReader;
		
		let s = "";
		let result = Database::parse_input(BufReader::new(s.as_bytes())).unwrap();
		assert!(result.is_empty());
		
		let s = "t # 0";
		let result = Database::parse_input(BufReader::new(s.as_bytes())).unwrap();
		assert_eq!(result, vec![
			RawInputGraph {
				nodes: Vec::new(),
				edges: Vec::new(),
			}
		]);
		
		let s = "t # 0\n\
		         v 0 15\n\
		         v 1 4\n
		         e 1 0 2";
		let result = Database::parse_input(BufReader::new(s.as_bytes())).unwrap();
		assert_eq!(result, vec![
			RawInputGraph {
				nodes: vec![
					RawInputNode { label: InputNodeLabel(15) },
					RawInputNode { label: InputNodeLabel(4)  },
				],
				edges: vec![
					RawInputEdge {
						from: InputNodeId(1), to: InputNodeId(0), label: InputEdgeLabel(2)
					},
				],
			},
		]);
		
		let s = "t # 0\n\
		         v 0 15\n\
		         v 1 4\n
		         e 1 0 2\n\
		         t # 1\n\
		         v 0 4\n\
		         v 1 15\n\
		         v 2 9\n\
		         v 3 4\n\
		         e 3 0 8\n\
		         e 2 3 8\n\
		         e 0 1 2\n\
		         e 0 2 4\n\
		         t # 2\n\
		         v 0 1\n\
		         v 1 2\n\
		         v 2 3\n\
		         v 3 4\n\
		         v 4 5\n\
		         v 5 6\n\
		         v 6 7\n\
		         e 0 1 2\n\
		         e 1 2 3\n\
		         e 2 3 4\n\
		         e 3 4 5\n\
		         e 4 5 6\n\
		         e 5 6 7\n";
		let result = Database::parse_input(BufReader::new(s.as_bytes())).unwrap();
		assert_eq!(result, vec![
			RawInputGraph {
				nodes: vec![
					RawInputNode { label: InputNodeLabel(15) },
					RawInputNode { label: InputNodeLabel(4)  },
				],
				edges: vec![
					RawInputEdge {
						from: InputNodeId(1), to: InputNodeId(0), label: InputEdgeLabel(2)
					},
				],
			},
			RawInputGraph {
				nodes: vec![
					RawInputNode { label: InputNodeLabel(4)  },
					RawInputNode { label: InputNodeLabel(15) },
					RawInputNode { label: InputNodeLabel(9)  },
					RawInputNode { label: InputNodeLabel(4)  },
				],
				edges: vec![
					RawInputEdge {
						from: InputNodeId(3), to: InputNodeId(0), label: InputEdgeLabel(8)
					},
					RawInputEdge {
						from: InputNodeId(2), to: InputNodeId(3), label: InputEdgeLabel(8)
					},
					RawInputEdge {
						from: InputNodeId(0), to: InputNodeId(1), label: InputEdgeLabel(2)
					},
					RawInputEdge {
						from: InputNodeId(0), to: InputNodeId(2), label: InputEdgeLabel(4)
					},
				],
			},
			RawInputGraph {
				nodes: vec![
					RawInputNode { label: InputNodeLabel(1) },
					RawInputNode { label: InputNodeLabel(2) },
					RawInputNode { label: InputNodeLabel(3) },
					RawInputNode { label: InputNodeLabel(4) },
					RawInputNode { label: InputNodeLabel(5) },
					RawInputNode { label: InputNodeLabel(6) },
					RawInputNode { label: InputNodeLabel(7) },
				],
				edges: vec![
					RawInputEdge {
						from: InputNodeId(0), to: InputNodeId(1), label: InputEdgeLabel(2)
					},
					RawInputEdge {
						from: InputNodeId(1), to: InputNodeId(2), label: InputEdgeLabel(3)
					},
					RawInputEdge {
						from: InputNodeId(2), to: InputNodeId(3), label: InputEdgeLabel(4)
					},
					RawInputEdge {
						from: InputNodeId(3), to: InputNodeId(4), label: InputEdgeLabel(5)
					},
					RawInputEdge {
						from: InputNodeId(4), to: InputNodeId(5), label: InputEdgeLabel(6)
					},
					RawInputEdge {
						from: InputNodeId(5), to: InputNodeId(6), label: InputEdgeLabel(7)
					},
				],
			},
		]);
	}
	
	#[test]
	fn test_count_labels() {
		use std::io::BufReader;
		
		let s = "t # 0\n\
		         v 0 15\n\
		         v 1 4\n
		         e 1 0 2\n\
		         t # 1\n\
		         v 0 4\n\
		         v 1 15\n\
		         v 2 9\n\
		         v 3 4\n\
		         e 3 0 8\n\
		         e 2 3 8\n\
		         e 0 1 2\n\
		         e 0 2 4\n\
		         t # 2\n\
		         v 0 1\n\
		         v 1 2\n\
		         v 2 3\n\
		         v 3 4\n\
		         v 4 5\n\
		         v 5 6\n\
		         v 6 7\n\
		         e 0 1 2\n\
		         e 1 2 3\n\
		         e 2 3 4\n\
		         e 3 4 5\n\
		         e 4 5 6\n\
		         e 5 6 7\n";
		let trees = Database::parse_input(BufReader::new(s.as_bytes())).unwrap();
		let (node_labels, edge_labels) = Database::count_labels(&trees);
		
		let expected_node_labels: HashMap<_,_> = std::array::IntoIter::new([
			(InputNodeLabel(1), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 2 }),
			(InputNodeLabel(2), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 2 }),
			(InputNodeLabel(3), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 2 }),
			(InputNodeLabel(4), DatabaseLabelCounts { frequency: 3, occurrence_count: 4, last_tid: 2 }),
			(InputNodeLabel(5), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 2 }),
			(InputNodeLabel(6), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 2 }),
			(InputNodeLabel(7), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 2 }),
			(InputNodeLabel(9), DatabaseLabelCounts { frequency: 1, occurrence_count: 1, last_tid: 1 }),
			(InputNodeLabel(15), DatabaseLabelCounts { frequency: 2, occurrence_count: 2, last_tid: 1 }),
		]).collect();
		
		assert_eq!(node_labels, expected_node_labels);
	}
}
