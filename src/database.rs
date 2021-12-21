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

#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct DatabaseTreeEdge {
	pub edgelabel: types::EdgeLabel,
	pub tonode: types::NodeId,
}

#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct DatabaseTreeNode {
	pub nodelabel: types::NodeLabel,
	pub edges: Vec<DatabaseTreeEdge>,
	pub mark: types::PatternMask, // Might not want these two here
	pub startmark: types::PatternMask,
}

impl DatabaseTreeNode {
	pub fn new(nodelabel: types::NodeLabel) -> DatabaseTreeNode {
		DatabaseTreeNode {
			nodelabel,
			edges: Vec::new(),
			mark: types::PatternMask(1),
			startmark: types::PatternMask(1)
		}
	}
}

#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct DatabaseTree {
	pub tid: types::Tid,
	pub nodes: Vec<DatabaseTreeNode>,
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
#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug, Clone)]
struct DatabaseLabelCounts {
	frequency: types::Frequency,
	occurrence_count: types::Frequency,
	last_tid: usize,
	id: usize,
}

impl DatabaseLabelCounts {
	fn new(frequency: types::Frequency, occurrence_count: types::Frequency, last_tid: usize) -> Self {
		Self { frequency, occurrence_count, last_tid, id: 0 }
	}
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
	pub fn read(filename: &str, min_freq: types::Frequency) -> Result<Database, DatabaseError> {
		let reader = std::io::BufReader::new(std::fs::File::open(filename)?);
		
		let trees = Self::parse_input(reader)?;
		
		let (mut node_labels, mut edge_labels) = Self::count_labels(&trees);

		Self::prune_and_assign_ids(&mut node_labels, min_freq);
		Self::prune_and_assign_ids(&mut edge_labels, min_freq);

		let trees = Self::prune_infrequent_nodes_and_edges(trees, &node_labels, &edge_labels, min_freq);
		
		Ok(Database {
			trees,
			node_labels: Vec::new(),
			edge_labels: Vec::new(),
			largest_n_nodes: 0,
			largest_n_edges: 0,
			edge_labels_indexes: Vec::new(),
		})
	}

	fn prune_and_assign_ids<K: std::hash::Hash + Eq>(labels: &mut HashMap<K, DatabaseLabelCounts>,
		min_freq: types::Frequency) {
		// Erase any infrequent labels
		labels.retain(|_,val| val.frequency >= min_freq);
		
		// Assign each label a unique ID
		labels.iter_mut()
			.enumerate()
			.for_each(|(id, (_, label))| label.id = id);
	}

	fn prune_infrequent_nodes_and_edges(mut trees: Vec<RawInputGraph>,
		node_labels: &HashMap<InputNodeLabel, DatabaseLabelCounts>,
		edge_labels: &HashMap<CombinedInputLabel, DatabaseLabelCounts>,
		min_freq: types::Frequency)
		-> Vec<DatabaseTree> {
		
		trees.iter_mut().enumerate().map(|(tid, tree)| {
			let nodes = &tree.nodes;
			tree.edges.retain(|e| edge_labels.contains_key(&Self::get_combined_label(e, nodes)));
			
			// Index will be None if the node is to be pruned, otherwise will be
			// index of the new node index.
			let mut node_id_map = vec![None; nodes.len()];

			// Initialize to a junk non-None value in first pass
			for edge in &tree.edges {
				node_id_map[edge.from.0 as usize] = Some(0);
				node_id_map[edge.to  .0 as usize] = Some(0);
			}

			// Assign new ids to nodes that are still included
			node_id_map.iter_mut()
				.filter(|id| id.is_some())
				.enumerate()
				.for_each(|(new_id, node_id)| *node_id = Some(new_id) );

			// Construct new tree, start with nodes
			let mut new_tree = DatabaseTree {
				tid: types::Tid(tid as u16),
				nodes: nodes.iter()
					.zip(node_id_map.iter())
					// Only add nodes with new indexes
					.filter(|(_,id)| id.is_some())
					// Map InputNodeLabels into NodeLabels
					.map(|(node,_)| DatabaseTreeNode::new(
						types::NodeLabel(node_labels.get(&node.label).unwrap().id as u8)))
					.collect()
			};

			// Add the edges
			for edge in &tree.edges {
				let edgelabel = types::EdgeLabel(edge_labels.get(&Self::get_combined_label(edge, nodes))
					.unwrap().id as u8);
				new_tree.nodes[edge.from.0 as usize].edges.push(DatabaseTreeEdge {
					edgelabel,
					tonode: types::NodeId(node_id_map[edge.to.0 as usize].unwrap() as u16)
				});
				new_tree.nodes[edge.to.0 as usize].edges.push(DatabaseTreeEdge {
					edgelabel,
					tonode: types::NodeId(node_id_map[edge.from.0 as usize].unwrap() as u16)
				});
			}

			new_tree
		})
		.collect()
	}

	fn get_combined_label(edge: &RawInputEdge, nodes: &[RawInputNode]) -> CombinedInputLabel {
		let node_label1 = nodes[edge.from.0 as usize].label;
		let node_label2 = nodes[edge.to  .0 as usize].label;
		if node_label1.0 > node_label2.0
			{ (node_label1, edge.label, node_label2) }
		else
			{ (node_label2, edge.label, node_label1) }
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
		let label = labels.entry(key).or_insert(DatabaseLabelCounts::new(1, 0, tid));
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
				Self::count_label(&mut edge_labels, Self::get_combined_label(&edge, &tree.nodes), tid);
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
			(InputNodeLabel(1), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(2), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(3), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(4), DatabaseLabelCounts::new(3, 4, 2)),
			(InputNodeLabel(5), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(6), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(7), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(9), DatabaseLabelCounts::new(1, 1, 1)),
			(InputNodeLabel(15), DatabaseLabelCounts::new(2, 2, 1)),
		]).collect();
		
		let expected_edge_labels: HashMap<_,_> = std::array::IntoIter::new([
			((InputNodeLabel(15), InputEdgeLabel(2), InputNodeLabel(4)),
				DatabaseLabelCounts::new(2, 2, 1)),
			((InputNodeLabel(4), InputEdgeLabel(8), InputNodeLabel(4)),
				DatabaseLabelCounts::new(1, 1, 1)),
			((InputNodeLabel(9), InputEdgeLabel(8), InputNodeLabel(4)),
				DatabaseLabelCounts::new(1, 1, 1)),
			((InputNodeLabel(9), InputEdgeLabel(4), InputNodeLabel(4)),
				DatabaseLabelCounts::new(1, 1, 1)),
			((InputNodeLabel(2), InputEdgeLabel(2), InputNodeLabel(1)),
				DatabaseLabelCounts::new(1, 1, 2)),
			((InputNodeLabel(3), InputEdgeLabel(3), InputNodeLabel(2)),
				DatabaseLabelCounts::new(1, 1, 2)),
			((InputNodeLabel(4), InputEdgeLabel(4), InputNodeLabel(3)),
				DatabaseLabelCounts::new(1, 1, 2)),
			((InputNodeLabel(5), InputEdgeLabel(5), InputNodeLabel(4)),
				DatabaseLabelCounts::new(1, 1, 2)),
			((InputNodeLabel(6), InputEdgeLabel(6), InputNodeLabel(5)),
				DatabaseLabelCounts::new(1, 1, 2)),
			((InputNodeLabel(7), InputEdgeLabel(7), InputNodeLabel(6)),
				DatabaseLabelCounts::new(1, 1, 2)),
		]).collect();
		
		assert_eq!(node_labels, expected_node_labels);
		assert_eq!(edge_labels, expected_edge_labels);
	}

	#[test]
	fn test_prune_and_assign_ids() {
		let expected_node_labels: HashMap<_,_> = std::array::IntoIter::new([
			(InputNodeLabel(1), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(2), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(3), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(4), DatabaseLabelCounts::new(3, 4, 2)),
			(InputNodeLabel(5), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(6), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(7), DatabaseLabelCounts::new(1, 1, 2)),
			(InputNodeLabel(9), DatabaseLabelCounts::new(1, 1, 1)),
			(InputNodeLabel(15), DatabaseLabelCounts::new(2, 2, 1)),
		]).collect();
		
		let mut copy = expected_node_labels.clone();
		// Removing no elements should only assign ids
		Database::prune_and_assign_ids(&mut copy, 0);
		
		assert_eq!(expected_node_labels.len(), copy.len());
		for id in 0..copy.len() {
			assert!(copy.iter().any(|(_, label)| label.id == id));
		}

		let mut copy = expected_node_labels.clone();
		Database::prune_and_assign_ids(&mut copy, 2);
		
		assert_eq!(copy.len(), 2);
		for id in 0..copy.len() {
			assert!(copy.iter().any(|(_, label)| label.id == id));
		}
		assert!(copy.contains_key(&InputNodeLabel(4)));
		assert!(copy.contains_key(&InputNodeLabel(15)));

		let mut copy = expected_node_labels.clone();
		Database::prune_and_assign_ids(&mut copy, 4);
		assert!(copy.is_empty());
	}
	
	#[test]
	fn test_infrequent_label_pruning() {
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
		
		let (mut node_labels, mut edge_labels) = Database::count_labels(&trees);

		Database::prune_and_assign_ids(&mut node_labels, 2);
		Database::prune_and_assign_ids(&mut edge_labels, 2);

		let result = Database::prune_infrequent_nodes_and_edges(trees, &node_labels, &edge_labels, 2);
		
		// (Note there is only one frequent edge label here, it must have ID 0)
		assert_eq!(result, vec![
			DatabaseTree {
				tid: types::Tid(0),
				nodes: vec![
					DatabaseTreeNode {
						nodelabel: types::NodeLabel(
							node_labels.get(&InputNodeLabel(15)).unwrap().id as u8),
						edges: vec![
							DatabaseTreeEdge {
								edgelabel: types::EdgeLabel(0),
								tonode: types::NodeId(1),
							}
						],
						mark: types::PatternMask(1),
						startmark: types::PatternMask(1),
					},
					DatabaseTreeNode {
						nodelabel: types::NodeLabel(
							node_labels.get(&InputNodeLabel(4)).unwrap().id as u8),
						edges: vec![
							DatabaseTreeEdge {
								edgelabel: types::EdgeLabel(0),
								tonode: types::NodeId(0),
							}
						],
						mark: types::PatternMask(1),
						startmark: types::PatternMask(1),
					},
				],
			},
			DatabaseTree {
				tid: types::Tid(1),
				nodes: vec![
					DatabaseTreeNode {
						nodelabel: types::NodeLabel(
							node_labels.get(&InputNodeLabel(4)).unwrap().id as u8),
						edges: vec![
							DatabaseTreeEdge {
								edgelabel: types::EdgeLabel(0),
								tonode: types::NodeId(1),
							}
						],
						mark: types::PatternMask(1),
						startmark: types::PatternMask(1),
					},
					DatabaseTreeNode {
						nodelabel: types::NodeLabel(
							node_labels.get(&InputNodeLabel(15)).unwrap().id as u8),
						edges: vec![
							DatabaseTreeEdge {
								edgelabel: types::EdgeLabel(0),
								tonode: types::NodeId(0),
							}
						],
						mark: types::PatternMask(1),
						startmark: types::PatternMask(1),
					},
				],
			},
			DatabaseTree {
				tid: types::Tid(2),
				nodes: Vec::new(),
			}
		]);
	}
}
