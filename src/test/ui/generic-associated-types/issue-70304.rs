// build-pass

#![feature(generic_associated_types)]
//~^ WARNING: the feature `generic_associated_types` is incomplete

trait Document {
    type Cursor<'a>: DocCursor<'a>;

    fn cursor(&self) -> Self::Cursor<'_>;
}

struct DocumentImpl {}

impl Document for DocumentImpl {
    type Cursor<'a> = DocCursorImpl<'a>;

    fn cursor(&self) -> Self::Cursor<'_> {
        DocCursorImpl {
            document: &self,
        }
    }
}




trait DocCursor<'a> {}

struct DocCursorImpl<'a> {
    document: &'a DocumentImpl,
}

impl<'a> DocCursor<'a> for DocCursorImpl<'a> {}





struct Lexer<'d, Cursor>
where
    Cursor: DocCursor<'d>,
{
    cursor: Cursor,
    _phantom: std::marker::PhantomData<&'d ()>,
}


impl<'d, Cursor> Lexer<'d, Cursor>
where
    Cursor: DocCursor<'d>,
{
    pub fn from<Doc>(document: &'d Doc) -> Lexer<'d, Cursor>
    where
        Doc: Document<Cursor<'d> = Cursor>,
    {
        Lexer {
            cursor: document.cursor(),
            _phantom: std::marker::PhantomData,
        }
    }
}



fn create_doc() -> impl Document {
    DocumentImpl {}
}

fn main() {
    let doc = create_doc();
    let lexer = Lexer::from(&doc);
}
