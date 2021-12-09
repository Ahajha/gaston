use crate::types;
use crate::tid_list;

pub struct InputEdgeLabel(i16);
pub struct InputNodeLabel(i16);
pub struct InputNodeId(i16);

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
	last_tid: types::Tid, // Would like to remove, is only used while reading
}

pub struct DatabaseEdgeLabel {
	pub input_edge_label: InputEdgeLabel,
	pub to_node_label: types::NodeLabel,
	pub from_node_label: types::NodeLabel,
	pub edge_label: types::EdgeLabel,
	pub frequency: types::Frequency,
	pub occurrence_count: types::Frequency,
	pub tid_list: tid_list::TidList,
	last_tid: types::Tid, // similar
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
	IncompleteGraphCommand(u32),
	IncompleteNodeCommand(u32),
	IncompleteEdgeCommand(u32),
	UnknownCommand(u32, String),
	ParseError(u32, std::num::ParseIntError),
	IOError(std::io::Error),
}

impl std::fmt::Display for DatabaseError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			Self::IncompleteGraphCommand(line_no) =>
				write!(f, "line {}: Incomplete graph, requires \"t # [id]\"", line_no),
			Self::IncompleteNodeCommand(line_no) =>
				write!(f, "line {}: Incomplete node, requires \"v [id] [label]", line_no),
			Self::IncompleteEdgeCommand(line_no) =>
				write!(f, "line {}: Incomplete edge, requires \"e [nodeid1] [nodeid2] [label]\"", line_no),
			Self::UnknownCommand(line_no, tok) =>
				write!(f, "line {}: Unknown command \"{}\", expected t, v, or e", line_no, tok),
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

enum Command {
	Graph(types::Tid),
	Node(InputNodeId, InputNodeLabel),
	Edge(InputNodeId, InputNodeId, InputEdgeLabel),
}

impl Database {
	pub fn read(filename: &str) -> Result<Database, DatabaseError> {
		
		Ok(Database {
			trees: Vec::new(),
			node_labels: Vec::new(),
			edge_labels: Vec::new(),
			largest_n_nodes: 0,
			largest_n_edges: 0,
			edge_labels_indexes: Vec::new(),
		})
	}
	
	// Returns an optional command (no command if the line is empty) parsed
	// from line.
	fn read_command((line_no, line): (u32, &str)) -> Result<Option<Command>, DatabaseError> {
		let mut token_iterator = line.split_whitespace();
		
		match token_iterator.next() {
			Some("t") => {
				// Errors here would be useless, so just skip the next token
				token_iterator.next();
				
				let tid = token_iterator
					.next()
					.ok_or(DatabaseError::IncompleteGraphCommand(line_no))?
					.parse()
					.map_err(|e| DatabaseError::ParseError(line_no, e))?;
				
				Ok(Some(Command::Graph(
					types::Tid(tid)
				)))
			},
			Some("v") => {
				let id = token_iterator
					.next()
					.ok_or(DatabaseError::IncompleteNodeCommand(line_no))?
					.parse()
					.map_err(|e| DatabaseError::ParseError(line_no, e))?;
				
				let label = token_iterator
					.next()
					.ok_or(DatabaseError::IncompleteNodeCommand(line_no))?
					.parse()
					.map_err(|e| DatabaseError::ParseError(line_no, e))?;
				
				Ok(Some(Command::Node(
					InputNodeId(id),
					InputNodeLabel(label)
				)))
			},
			Some("e") => {
				let nodeid1 = token_iterator
					.next()
					.ok_or(DatabaseError::IncompleteEdgeCommand(line_no))?
					.parse()
					.map_err(|e| DatabaseError::ParseError(line_no, e))?;
				
				let nodeid2 = token_iterator
					.next()
					.ok_or(DatabaseError::IncompleteEdgeCommand(line_no))?
					.parse()
					.map_err(|e| DatabaseError::ParseError(line_no, e))?;
				
				let label = token_iterator
					.next()
					.ok_or(DatabaseError::IncompleteEdgeCommand(line_no))?
					.parse()
					.map_err(|e| DatabaseError::ParseError(line_no, e))?;
				
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
