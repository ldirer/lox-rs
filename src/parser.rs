use std::iter::Peekable;

use crate::ast::Statement::ReturnStatement;
use crate::ast::{
    BinaryLogicalOperator, BinaryLogicalOperatorType, BinaryOperator, BinaryOperatorType, Expr,
    FunctionParameter, FunctionType, Literal, Statement, UnaryOperator, UnaryOperatorType,
};
use crate::token::{Token, TokenType};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum ParserError {
    #[error("[line {line}] Error at {lexeme}: Expect ')' after expression.")]
    UnmatchedParenthesis { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ';' after value.")]
    MissingSemicolonPrint { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ';' after expression.")]
    MissingSemicolonExpressionStatement { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ';' after loop condition.")]
    MissingSemicolonLoopCondition { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect variable name.")]
    InvalidSyntaxVarDeclaration { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ';' after variable declaration.")]
    MissingSemicolonVariableDeclaration { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Invalid assignment target.")]
    InvalidAssignmentTarget { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Unclosed block, expected '}}'.")]
    UnclosedBlock { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect '(' after 'while'.")]
    MissingOpeningParenthesisWhile { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ')' after condition.")]
    MissingClosingParenthesisCondition { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect '(' after 'if'.")]
    MissingOpeningParenthesisIf { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect '(' after 'for'.")]
    MissingOpeningParenthesisFor { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ')' after 'for' clauses.")]
    MissingClosingParenthesisFor { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect ')' after arguments.")]
    MissingClosingParenthesisInCall { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect {function_type} name.")]
    FunctionIdentifierExpected {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },
    #[error("[line {line}] Error at {lexeme}: Expect class name.")]
    ClassIdentifierExpected { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect '{{' after class name.")]
    MissingOpeningBraceClass { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect '}}' after method declarations.")]
    MissingClosingBraceClass { line: usize, lexeme: String },

    #[error("[line {line}] Error at {lexeme}: Expect '(' after {function_type} name.")]
    MissingOpeningParenthesisFunction {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },
    #[error("[line {line}] Error at {lexeme}: Expect {function_type} parameter identifier.")]
    FunctionExpectedParameterName {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },
    #[error("[line {line}] Error at {lexeme}: Expect ')' after parameters.")]
    MissingClosingParenthesisFunction {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },
    #[error("[line {line}] Error at {lexeme}: Expect '{{' before {function_type} body.")]
    MissingOpeningBraceFunction {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },
    #[error("[line {line}] Error at {lexeme}: Expect '}}' to close {function_type} body.")]
    MissingClosingBraceFunction {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },

    #[error("[line {line}] Error at {lexeme}: Expect expression.")]
    ExpectExpression { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Can't have more than 255 parameters.")]
    FunctionTooManyParameters {
        function_type: FunctionType,
        line: usize,
        lexeme: String,
    },

    #[error("[line {line}] Error at {lexeme}: Can't have more than 255 arguments.")]
    FunctionCallTooManyArguments { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect property name after '.'.")]
    ExpectPropertyAccessName { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect superclass name.")]
    ExpectSuperclassName { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect '.' after 'super'.")]
    ExpectDotAfterSuper { line: usize, lexeme: String },
    #[error("[line {line}] Error at {lexeme}: Expect superclass method name.")]
    ExpectMethodAfterSuper { line: usize, lexeme: String },
}

pub struct Parser<T: Iterator<Item = Token>> {
    tokens: Peekable<T>,
    previous_token: Option<Token>,
    errors: Vec<ParserError>,
}

pub fn parse<T>(tokens: T) -> Result<Vec<Statement>, Vec<ParserError>>
where
    T: Iterator<Item = Token>,
{
    let mut parser = Parser::new(tokens);
    let statements = parser.parse_program();
    if parser.errors.len() > 0 {
        // a result might not be the best interface, we could imagine wanting to access statements even if there were errors.
        // but it's sufficient for our use.
        return Err(parser.errors);
    }
    Ok(statements)
}

impl<T: Iterator<Item = Token>> Parser<T> {
    pub(crate) fn new(tokens: T) -> Self {
        let tokens = tokens.peekable();
        Parser {
            tokens,
            previous_token: None,
            errors: vec![],
        }
    }

    // clean error handling not the focus yet
    pub fn parse_program(&mut self) -> Vec<Statement> {
        let mut statements: Vec<Statement> = vec![];
        while !self.is_at_end() {
            match self.safe_parse_declaration() {
                None => {}
                Some(statement) => statements.push(statement),
            }
        }
        statements
    }

    pub fn safe_parse_declaration(&mut self) -> Option<Statement> {
        let parsed = self.parse_declaration();
        match parsed {
            Ok(statement) => Some(statement),
            Err(err) => {
                self.errors.push(err);
                self.recover();
                return None;
            }
        }
    }

    pub fn parse_declaration(&mut self) -> Result<Statement, ParserError> {
        if self.match_current(&vec![TokenType::Fun]).is_some() {
            return self.parse_function_declaration(FunctionType::Function);
        }

        if self.match_current(&vec![TokenType::Class]).is_some() {
            return self.parse_class_declaration();
        }
        match self.match_current(&vec![TokenType::Var]) {
            Some(_) => self.parse_var_declaration(),
            None => self.parse_statement(),
        }
    }

    fn parse_class_declaration(&mut self) -> Result<Statement, ParserError> {
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        let name_token = self.consume(
            TokenType::Identifier,
            ParserError::ClassIdentifierExpected { line, lexeme },
        )?;
        let mut superclass = None;

        if self.match_current(&vec![TokenType::Less]).is_some() {
            let TokenInfo { line, lexeme } = self.get_current_token_info();
            let superclass_token = self.consume(
                TokenType::Identifier,
                ParserError::ExpectSuperclassName { line, lexeme },
            )?;
            superclass = Some(Expr::Variable {
                name: superclass_token.lexeme,
                line: superclass_token.line,
                depth: None,
            });
        }

        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::LeftBrace,
            ParserError::MissingOpeningBraceClass { line, lexeme },
        )?;

        let mut methods = vec![];
        while !self.is_at_end() && self.check(&TokenType::RightBrace).is_none() {
            methods.push(self.parse_function_declaration(FunctionType::Method)?);
        }

        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::RightBrace,
            ParserError::MissingClosingBraceClass { line, lexeme },
        )?;

        Ok(Statement::ClassDeclaration {
            name: name_token.lexeme,
            superclass: superclass.map(Box::new),
            line: name_token.line,
            methods,
        })
    }

    fn parse_function_declaration(
        &mut self,
        function_type: FunctionType,
    ) -> Result<Statement, ParserError> {
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        let name_token = self.consume(
            TokenType::Identifier,
            ParserError::FunctionIdentifierExpected {
                function_type,
                line,
                lexeme,
            },
        )?;

        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::LeftParen,
            ParserError::MissingOpeningParenthesisFunction {
                function_type,
                line,
                lexeme,
            },
        )?;
        let mut parameters = vec![];
        if self
            .tokens
            .peek()
            .is_some_and(|t| t.r#type != TokenType::RightParen)
        {
            loop {
                let token = self.match_current(&vec![TokenType::Identifier]);
                match token {
                    None => {
                        let TokenInfo { line, lexeme } = self.get_current_token_info();
                        return Err(ParserError::FunctionExpectedParameterName {
                            function_type,
                            line,
                            lexeme,
                        });
                    }
                    Some(t) => {
                        parameters.push(FunctionParameter {
                            name: t.lexeme.clone(),
                            line: t.line,
                        });
                        if parameters.len() > 255 {
                            // we should not stop parsing here. We want to report the error but the parser is in a clean state.
                            self.errors.push(ParserError::FunctionTooManyParameters {
                                function_type,
                                line: t.line,
                                lexeme: error_lexeme(&t),
                            });
                        }
                    }
                }
                if self.match_current(&vec![TokenType::Comma]).is_none() {
                    break;
                }
            }
        }

        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::RightParen,
            ParserError::MissingClosingParenthesisFunction {
                function_type,
                line,
                lexeme,
            },
        )?;
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::LeftBrace,
            ParserError::MissingOpeningBraceFunction {
                function_type,
                line,
                lexeme,
            },
        )?;
        let body = self.parse_block()?;
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::RightBrace,
            ParserError::MissingClosingBraceFunction {
                function_type,
                line,
                lexeme,
            },
        )?;

        Ok(Statement::FunctionDeclaration {
            line: name_token.line,
            parameters,
            body,
            name: name_token.lexeme,
        })
    }

    fn parse_var_declaration(&mut self) -> Result<Statement, ParserError> {
        match self.match_current(&vec![TokenType::Identifier]) {
            None => {
                let TokenInfo { line, lexeme } = self.get_current_token_info();
                return Err(ParserError::InvalidSyntaxVarDeclaration { line, lexeme });
            }
            Some(Token {
                r#type: TokenType::Identifier,
                lexeme: name,
                line: line_declaration,
            }) => {
                let mut initializer = Expr::Literal(Literal::Nil);
                if self.match_current(&vec![TokenType::Equal]).is_some() {
                    initializer = self.parse_expression()?;
                }

                let TokenInfo { line, lexeme } = self.get_current_token_info();
                self.consume(
                    TokenType::Semicolon,
                    ParserError::MissingSemicolonVariableDeclaration { line, lexeme },
                )?;

                Ok(Statement::VarDeclaration {
                    initializer,
                    name,
                    line: line_declaration,
                })
            }
            Some(t) => unreachable!("unexpected token type for {:?}", t),
        }
    }

    pub(crate) fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        if self.match_current(&vec![TokenType::Print]).is_some() {
            return self.parse_print_statement();
        }
        if self.match_current(&vec![TokenType::Return]).is_some() {
            return self.parse_return_statement();
        }

        if self.match_current(&vec![TokenType::For]).is_some() {
            return self.parse_for_statement();
        }
        if self.match_current(&vec![TokenType::If]).is_some() {
            return self.parse_if_statement();
        }

        if self.match_current(&vec![TokenType::While]).is_some() {
            return self.parse_while_statement();
        }
        if self.match_current(&vec![TokenType::LeftBrace]).is_some() {
            let block = Statement::Block {
                statements: self.parse_block()?,
            };

            let TokenInfo { line, lexeme } = self.get_current_token_info();
            self.consume(
                TokenType::RightBrace,
                ParserError::UnclosedBlock { line, lexeme },
            )?;
            return Ok(block);
        }
        self.parse_expression_statement()
    }
    /// all of these are allowed. Omitted condition implies 'true'
    /// for (var i = 0; i < 10; i = i + 1) print i;
    /// for (; i < 10; i = i + 1) print i;
    /// for (; i < 10; i = i + 1) print i;
    /// for (; ; i = i + 1) print i;
    /// for (; ; ) print i;
    fn parse_for_statement(&mut self) -> Result<Statement, ParserError> {
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::LeftParen,
            ParserError::MissingOpeningParenthesisFor { line, lexeme },
        )?;
        let initializer = if self.match_current(&vec![TokenType::Semicolon]).is_some() {
            None
        } else if self.match_current(&vec![TokenType::Var]).is_some() {
            Some(self.parse_var_declaration()?)
        } else {
            Some(self.parse_expression_statement()?)
        };

        let mut condition = None;
        if self.match_current(&vec![TokenType::Semicolon]).is_none() {
            condition = Some(self.parse_expression()?);
            let TokenInfo { line, lexeme } = self.get_current_token_info();
            self.consume(
                TokenType::Semicolon,
                ParserError::MissingSemicolonLoopCondition { line, lexeme },
            )?;
        }

        let mut increment = None;
        if self.match_current(&vec![TokenType::RightParen]).is_none() {
            increment = Some(self.parse_expression()?);
            let TokenInfo { line, lexeme } = self.get_current_token_info();
            self.consume(
                TokenType::RightParen,
                ParserError::MissingClosingParenthesisFor { line, lexeme },
            )?;
        }

        let for_body: Statement = self.parse_statement()?;

        let mut while_body_statements = vec![for_body];
        if let Some(increment_expr) = increment {
            while_body_statements.push(Statement::ExprStatement {
                expression: increment_expr,
            });
        }

        let while_statement = Statement::WhileStatement {
            condition: condition.unwrap_or(Expr::Literal(Literal::True)),
            body: Box::new(Statement::Block {
                statements: while_body_statements,
            }),
        };
        let statements: Vec<Statement> = vec![initializer, Some(while_statement)]
            .into_iter()
            .filter_map(|s| s)
            .collect();

        Ok(Statement::Block { statements })
    }

    fn parse_if_statement(&mut self) -> Result<Statement, ParserError> {
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::LeftParen,
            ParserError::MissingOpeningParenthesisIf { line, lexeme },
        )?;
        let condition = self.parse_expression()?;

        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::RightParen,
            ParserError::MissingClosingParenthesisCondition { line, lexeme },
        )?;
        let then_branch = self.parse_statement()?;

        let mut else_branch = None;
        if self.match_current(&vec![TokenType::Else]).is_some() {
            else_branch = Some(self.parse_statement()?);
        }
        Ok(Statement::IfStatement {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: else_branch.map(Box::new),
        })
    }
    fn parse_while_statement(&mut self) -> Result<Statement, ParserError> {
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::LeftParen,
            ParserError::MissingOpeningParenthesisWhile { line, lexeme },
        )?;
        let condition = self.parse_expression()?;
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::RightParen,
            ParserError::MissingClosingParenthesisCondition { line, lexeme },
        )?;
        let body = self.parse_statement()?;
        Ok(Statement::WhileStatement {
            condition,
            body: Box::new(body),
        })
    }

    fn parse_block(&mut self) -> Result<Vec<Statement>, ParserError> {
        let mut statements = vec![];
        while !self.is_at_end()
            && !self
                .tokens
                .peek()
                .is_some_and(|t| t.r#type == TokenType::RightBrace)
        {
            match self.safe_parse_declaration() {
                None => {}
                Some(statement) => statements.push(statement),
            }
        }
        Ok(statements)
    }

    fn parse_print_statement(&mut self) -> Result<Statement, ParserError> {
        let expr = self.parse_expression()?;
        let token_match = self.match_current(&vec![TokenType::Semicolon]);
        match token_match {
            None => {
                let TokenInfo { line, lexeme } = self.get_current_token_info();
                Err(ParserError::MissingSemicolonPrint { line, lexeme })
            }
            Some(_) => Ok(Statement::PrintStatement { expression: expr }),
        }
    }

    fn parse_return_statement(&mut self) -> Result<Statement, ParserError> {
        let return_line = self.previous_token.as_ref().unwrap().line;
        let mut expr = None;
        if self
            .tokens
            .peek()
            .is_some_and(|t| t.r#type != TokenType::Semicolon)
        {
            expr = Some(self.parse_expression()?);
        }

        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::Semicolon,
            ParserError::MissingSemicolonExpressionStatement { line, lexeme },
        )?;
        return Ok(ReturnStatement {
            expression: expr,
            line: return_line,
        });
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParserError> {
        let expr = self.parse_expression()?;
        let token_match = self.match_current(&vec![TokenType::Semicolon]);
        match token_match {
            None => {
                let TokenInfo { line, lexeme } = self.get_current_token_info();
                Err(ParserError::MissingSemicolonExpressionStatement { line, lexeme })
            }
            Some(_) => Ok(Statement::ExprStatement { expression: expr }),
        }
    }

    /// parsing functions encode grammar rules. This code should be read with the grammar.
    /// in particular, the grammar used here (from the book) encodes precedence rules.
    pub(crate) fn parse_expression(&mut self) -> Result<Expr, ParserError> {
        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParserError> {
        let expr = self.parse_logical_or()?;
        match (self.match_current(&vec![TokenType::Equal]), &expr) {
            (None, _) => Ok(expr),
            (Some(_), Expr::Variable { .. }) => {
                let value = self.parse_assignment()?;
                Ok(Expr::Assign {
                    location: Box::from(expr),
                    value: Box::new(value),
                })
            }
            (Some(_), Expr::PropertyAccess { object, name, line }) => {
                let value = self.parse_assignment()?;
                Ok(Expr::Set {
                    object: object.clone(),
                    name: name.clone(),
                    value: Box::new(value),
                    line: *line,
                })
            }
            (Some(token), _) => Err(ParserError::InvalidAssignmentTarget {
                line: token.line,
                lexeme: error_lexeme(&token),
            }),
        }
    }

    fn parse_logical_or(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_logical_and()?;
        while let Some(token) = self.match_current(&vec![TokenType::Or]) {
            let right = self.parse_logical_and()?;
            expr = Expr::BinaryLogical {
                operator: BinaryLogicalOperator {
                    type_: BinaryLogicalOperatorType::Or,
                    line: token.line,
                },
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn parse_logical_and(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_equality()?;
        while let Some(token) = self.match_current(&vec![TokenType::And]) {
            let right = self.parse_equality()?;
            expr = Expr::BinaryLogical {
                operator: BinaryLogicalOperator {
                    type_: BinaryLogicalOperatorType::And,
                    line: token.line,
                },
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_comparison()?;
        while let Some(token) =
            self.match_current(&vec![TokenType::BangEqual, TokenType::EqualEqual])
        {
            let operator = token_to_binary(token);
            let right = self.parse_comparison()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }

        return Ok(expr);
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_term()?;
        while let Some(token) = self.match_current(&vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let operator = token_to_binary(token);
            let right = self.parse_term()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_term(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_factor()?;
        while let Some(token) = self.match_current(&vec![TokenType::Plus, TokenType::Minus]) {
            let operator = token_to_binary(token);
            let right = self.parse_factor()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn parse_factor(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_unary()?;
        while let Some(token) = self.match_current(&vec![TokenType::Slash, TokenType::Star]) {
            let operator = token_to_binary(token);
            let right = self.parse_unary()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParserError> {
        while let Some(token) = self.match_current(&vec![TokenType::Bang, TokenType::Minus]) {
            let operator = token_to_unary(token);
            let operand = self.parse_unary()?;
            return Ok(Expr::Unary {
                operator,
                expression: Box::new(operand),
            });
        }
        self.parse_call()
    }

    fn parse_call(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_primary()?;
        // reminder that this is a while loop because we match chained calls
        loop {
            if self.match_current(&vec![TokenType::Dot]).is_some() {
                let TokenInfo { line, lexeme } = self.get_current_token_info();
                let identifier = self.consume(
                    TokenType::Identifier,
                    ParserError::ExpectPropertyAccessName { line, lexeme },
                )?;
                expr = Expr::PropertyAccess {
                    object: Box::new(expr),
                    line: identifier.line,
                    name: identifier.lexeme,
                }
            } else if let Some(parenthesis_token) = self.match_current(&vec![TokenType::LeftParen])
            {
                let args = self.parse_function_arguments()?;
                expr = Expr::FunctionCall {
                    line: parenthesis_token.line,
                    callee: Box::new(expr),
                    arguments: args,
                };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn parse_function_arguments(&mut self) -> Result<Vec<Expr>, ParserError> {
        let mut args = vec![];
        if self
            .tokens
            .peek()
            .is_some_and(|t| t.r#type != TokenType::RightParen)
        {
            args.push(self.parse_expression()?);
            while self.match_current(&vec![TokenType::Comma]).is_some() {
                args.push(self.parse_expression()?);
                if args.len() > 255 {
                    self.errors.push(ParserError::FunctionCallTooManyArguments {
                        line: self.previous_token.as_ref().unwrap().line,
                        lexeme: error_lexeme(self.previous_token.as_ref().unwrap()),
                    });
                }
            }
        }
        let TokenInfo { line, lexeme } = self.get_current_token_info();
        self.consume(
            TokenType::RightParen,
            ParserError::MissingClosingParenthesisInCall { line, lexeme },
        )?;

        Ok(args)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let token = self.advance();

        if token.is_none() {
            panic!("unfinished business?")
        }
        let token = token.unwrap();
        match token.r#type {
            TokenType::This => Ok(Expr::This(Box::new(Expr::Variable {
                line: token.line,
                name: "this".to_string(),
                depth: None,
            }))),
            TokenType::Identifier => Ok(Expr::Variable {
                name: token.lexeme,
                line: token.line,
                depth: None,
            }),
            TokenType::False => Ok(Expr::Literal(Literal::False)),
            TokenType::True => Ok(Expr::Literal(Literal::True)),
            TokenType::Nil => Ok(Expr::Literal(Literal::Nil)),
            TokenType::Number => Ok(Expr::Literal(Literal::Number(
                token.lexeme.parse().unwrap(),
            ))),
            // remove quotes from string
            TokenType::String => Ok(Expr::Literal(Literal::String(
                token.lexeme[1..token.lexeme.len() - 1].to_string(),
            ))),
            TokenType::LeftParen => {
                let expr = self.parse_expression()?;
                match self.match_current(&vec![TokenType::RightParen]) {
                    None => {
                        let TokenInfo { line, lexeme } = self.get_current_token_info();
                        Err(ParserError::UnmatchedParenthesis { line, lexeme })
                    }
                    Some(_) => Ok(Expr::Grouping(Box::new(expr))),
                }
            }
            TokenType::Super => {
                let TokenInfo { line, lexeme } = self.get_current_token_info();
                self.consume(
                    TokenType::Dot,
                    ParserError::ExpectDotAfterSuper { line, lexeme },
                )?;
                let TokenInfo { line, lexeme } = self.get_current_token_info();
                let method_token = self.consume(
                    TokenType::Identifier,
                    ParserError::ExpectMethodAfterSuper { line, lexeme },
                )?;
                Ok(Expr::Super {
                    variable: Box::new(Expr::Variable {
                        depth: None,
                        line,
                        name: "super".to_string(),
                    }),
                    line,
                    method: method_token.lexeme,
                })
            }
            _ => Err(ParserError::ExpectExpression {
                line: token.line,
                lexeme: error_lexeme(&token),
            }),
        }
    }

    /// a better api for this might be to return an Option<Token>
    fn match_current(&mut self, token_types: &Vec<TokenType>) -> Option<Token> {
        for token_type in token_types {
            if self.check(token_type).is_some() {
                return self.advance();
            }
        }
        None
    }
    fn check(&mut self, token_type: &TokenType) -> Option<&Token> {
        self.tokens.peek().filter(|t| &t.r#type == token_type)
    }

    fn advance(&mut self) -> Option<Token> {
        let token = self.tokens.next();
        self.previous_token = token.clone();
        token
    }

    fn consume(&mut self, token_type: TokenType, err: ParserError) -> Result<Token, ParserError> {
        match self.match_current(&vec![token_type]) {
            None => Err(err),
            Some(t) => Ok(t),
        }
    }

    #[allow(clippy::wrong_self_convention)]
    fn is_at_end(&mut self) -> bool {
        // we check two things. Does not feel clean.
        self.tokens.peek().is_none()
            || self
                .tokens
                .peek()
                .is_some_and(|t| t.r#type == TokenType::EOF)
    }

    /// 'synchronize' in the book.
    /// The idea is that when there's an error, we don't want to show many 'cascading errors'.
    /// So we use 'anchor points' in tokens where it's likely we are back to a clean state.
    fn recover(&mut self) {
        while let Some(token) = self.tokens.peek() {
            // I think there's something nice about having an explicit match statement here: if we
            // make additions to the language, it lets us know we need to consider what we want to
            // do with the new token type here.
            match token.r#type {
                TokenType::Semicolon => {
                    self.advance();
                    return;
                }
                TokenType::EOF => return,
                TokenType::Class => return,
                TokenType::Fun => return,
                TokenType::For => return,
                TokenType::If => return,
                TokenType::Print => return,
                TokenType::Return => return,
                TokenType::Var => return,
                TokenType::While => return,
                TokenType::LeftParen => {}
                TokenType::RightParen => {}
                TokenType::LeftBrace => {}
                TokenType::RightBrace => {}
                TokenType::Comma => {}
                TokenType::Dot => {}
                TokenType::Minus => {}
                TokenType::Plus => {}
                TokenType::Slash => {}
                TokenType::Star => {}
                TokenType::Bang => {}
                TokenType::BangEqual => {}
                TokenType::Equal => {}
                TokenType::EqualEqual => {}
                TokenType::Greater => {}
                TokenType::GreaterEqual => {}
                TokenType::Less => {}
                TokenType::LessEqual => {}
                TokenType::And => {}
                TokenType::Else => {}
                TokenType::False => {}
                TokenType::Nil => {}
                TokenType::Or => {}
                TokenType::Super => {}
                TokenType::This => {}
                TokenType::True => {}
                TokenType::Identifier => {}
                TokenType::String => {}
                TokenType::Number => {}
            }
            self.advance();
        }
    }

    /// admittedly the way this is used is a bit lame. It works...
    fn get_current_token_info(&mut self) -> TokenInfo {
        let token = self.tokens.peek().unwrap();
        let line = token.line;
        let lexeme = error_lexeme(token);
        return TokenInfo { line, lexeme };
    }
}

/// hack to make sure error messages match the official test suite
fn error_lexeme(token: &Token) -> String {
    let mut lexeme = format!("'{}'", token.lexeme.clone());
    if token.r#type == TokenType::EOF {
        lexeme = "end".to_string();
    }
    lexeme
}

struct TokenInfo {
    line: usize,
    lexeme: String,
}

/// One thing I wish was better here:
/// Nothing tells us if we forgot one operator. Ideally I'd like to know that all UnaryOperators/BinaryOperators can be produced by these functions.
fn token_to_unary(token: Token) -> UnaryOperator {
    match token.r#type {
        TokenType::Minus => UnaryOperator {
            type_: UnaryOperatorType::Minus,
            line: token.line,
        },
        TokenType::Bang => UnaryOperator {
            type_: UnaryOperatorType::Not,
            line: token.line,
        },
        _ => panic!("unable to parse token into unary operator: {:?}", token),
    }
}

fn token_to_binary(token: Token) -> BinaryOperator {
    match token.r#type {
        TokenType::Plus => BinaryOperator {
            type_: BinaryOperatorType::Plus,
            line: token.line,
        },
        TokenType::Minus => BinaryOperator {
            type_: BinaryOperatorType::Minus,
            line: token.line,
        },
        TokenType::Star => BinaryOperator {
            type_: BinaryOperatorType::Multiply,
            line: token.line,
        },
        TokenType::Slash => BinaryOperator {
            type_: BinaryOperatorType::Divide,
            line: token.line,
        },
        TokenType::EqualEqual => BinaryOperator {
            type_: BinaryOperatorType::Eq,
            line: token.line,
        },
        TokenType::BangEqual => BinaryOperator {
            type_: BinaryOperatorType::Neq,
            line: token.line,
        },
        TokenType::Greater => BinaryOperator {
            type_: BinaryOperatorType::Gt,
            line: token.line,
        },
        TokenType::GreaterEqual => BinaryOperator {
            type_: BinaryOperatorType::Gte,
            line: token.line,
        },
        TokenType::Less => BinaryOperator {
            type_: BinaryOperatorType::Lt,
            line: token.line,
        },
        TokenType::LessEqual => BinaryOperator {
            type_: BinaryOperatorType::Lte,
            line: token.line,
        },
        _ => panic!("unable to parse token into binary operator: {:?}", token),
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Literal::Number;
    use crate::ast::Statement::{ExprStatement, ReturnStatement};
    use crate::ast::{
        format_lisp_like, BinaryLogicalOperator, BinaryLogicalOperatorType, BinaryOperator,
        BinaryOperatorType, Expr, FunctionParameter, Literal, Statement, UnaryOperator,
        UnaryOperatorType,
    };
    use crate::parser::{Parser, ParserError};
    use crate::test_helpers::{parse_expr, parse_program, parse_statement};
    use crate::token::{Token, TokenType};

    #[test]
    fn test_match_current() {
        let tokens = vec![Token {
            r#type: TokenType::Plus,
            lexeme: "+".to_string(),
            line: 1,
        }];
        let mut parser = Parser::new(tokens.into_iter());
        let matched = parser.match_current(&vec![TokenType::Plus]);
        assert!(matched.is_some());
        // cursor should have moved
        let matched_again = parser.match_current(&vec![TokenType::Plus]);
        assert!(matched_again.is_none());
    }

    #[test]
    fn test_binary_simple() {
        let expr = parse_expr("1 + 2").unwrap();
        assert_eq!(
            expr,
            Expr::Binary {
                operator: BinaryOperator {
                    type_: BinaryOperatorType::Plus,
                    line: 1
                },
                left: Box::new(Expr::Literal(Literal::Number(1.),)),
                right: Box::new(Expr::Literal(Literal::Number(2.),))
            }
        )
    }

    #[test]
    fn test_binary_logical() {
        let expr = parse_expr("1 or 2").unwrap();
        assert_eq!(
            expr,
            Expr::BinaryLogical {
                operator: BinaryLogicalOperator {
                    type_: BinaryLogicalOperatorType::Or,
                    line: 1
                },
                left: Box::new(Expr::Literal(Literal::Number(1.),)),
                right: Box::new(Expr::Literal(Literal::Number(2.),))
            }
        )
    }

    #[test]
    fn test_unary_simple() {
        let expr = parse_expr("-2").unwrap();
        assert_eq!(
            expr,
            Expr::Unary {
                operator: UnaryOperator {
                    type_: UnaryOperatorType::Minus,
                    line: 1
                },
                expression: Box::new(Expr::Literal(Literal::Number(2.)))
            }
        )
    }

    #[test]
    fn test_precedence() {
        let expr = parse_expr("3 + 2 * (-2 + 3) == 5").unwrap();

        // I'd use RPN but I don't understand it :)
        // "3 2 2 - 3 + * + 5 =="
        assert_eq!(
            format_lisp_like(&expr),
            "(== (+ 3 (* 2 (group (+ (- 2) 3)))) 5)"
        )
    }

    #[test]
    fn test_unmatched_parenthesis() {
        let expr = parse_expr("\n((1 + 2) / 1");
        assert!(expr.is_err());
        let err = expr.err().unwrap();
        assert_eq!(
            err,
            ParserError::UnmatchedParenthesis {
                line: 2,
                lexeme: "end".to_string()
            }
        );
    }
    #[test]
    fn test_unfinished_expression() {
        let expr = parse_expr("1 + ");
        assert!(expr.is_err());
        let err = expr.err().unwrap();
        assert_eq!(
            err,
            ParserError::ExpectExpression {
                line: 1,
                lexeme: "end".to_string()
            }
        );
    }

    #[test]
    fn test_print_statement() {
        let statement = parse_statement("print 1;").unwrap();
        assert_eq!(
            statement,
            Statement::PrintStatement {
                expression: Expr::Literal(Number(1.))
            }
        )
    }

    #[test]
    fn test_statement_missing_semicolon() {
        [
            (
                "1 + 3",
                ParserError::MissingSemicolonExpressionStatement {
                    lexeme: "end".to_string(),
                    line: 1,
                },
            ),
            (
                "print 1 + 3",
                ParserError::MissingSemicolonPrint {
                    lexeme: "end".to_string(),
                    line: 1,
                },
            ),
        ]
        .into_iter()
        .for_each(|(code, expected_error)| {
            let err = parse_statement(code).unwrap_err();
            assert_eq!(err, expected_error);
        })
    }

    #[test]
    fn test_variable_declaration() {
        let parsed = parse_program("var a = 1;").unwrap();
        assert_eq!(parsed.len(), 1);
    }
    #[test]
    fn test_variable_declaration_no_initializer() {
        let parsed = parse_program("var a;").unwrap();
        assert_eq!(parsed.len(), 1);
    }
    #[test]
    fn test_function_declaration() {
        let parsed = parse_program("fun fibonacci(n, debug) { return n + 1;}").unwrap();
        assert_eq!(parsed.len(), 1);
        assert_eq!(
            parsed[0],
            Statement::FunctionDeclaration {
                line: 1,
                name: "fibonacci".to_string(),
                parameters: vec![
                    FunctionParameter {
                        name: "n".to_string(),
                        line: 1
                    },
                    FunctionParameter {
                        name: "debug".to_string(),
                        line: 1
                    }
                ],
                body: vec![ReturnStatement {
                    line: 1,
                    expression: Some(Expr::Binary {
                        operator: BinaryOperator {
                            type_: BinaryOperatorType::Plus,
                            line: 1
                        },
                        left: Box::from(Expr::Variable {
                            line: 1,
                            name: "n".to_string(),
                            depth: None,
                        }),
                        right: Box::from(Expr::Literal(Number(1.0)))
                    })
                }]
            }
        );
    }
    #[test]
    fn test_variable_expression() {
        // this is valid at this stage, the parser allows undefined variables (interpreter would throw a runtime error)
        let parsed = parse_program("a + b == 3;").unwrap();
        assert_eq!(parsed.len(), 1);
    }
    #[test]
    fn test_variable_assignment() {
        let parsed = parse_program("a = 3;").unwrap();
        assert_eq!(parsed.len(), 1);
        assert_eq!(
            parsed[0],
            ExprStatement {
                expression: Expr::Assign {
                    value: Box::from(Expr::Literal(Number(3.))),
                    location: Box::from(Expr::Variable {
                        name: "a".to_string(),
                        line: 1,
                        depth: None,
                    })
                }
            }
        );
    }

    #[test]
    fn test_function_call() {
        let parsed = parse_expr("caller(1, 2)").unwrap();
        assert_eq!(
            parsed,
            Expr::FunctionCall {
                callee: Box::from(Expr::Variable {
                    depth: None,
                    line: 1,
                    name: "caller".to_string()
                }),
                line: 1,
                arguments: vec![
                    Expr::Literal(Literal::Number(1.)),
                    Expr::Literal(Literal::Number(2.))
                ],
            }
        );
    }

    #[test]
    fn test_for_loop() {
        let parsed = parse_statement("for (;;) { print 1;}").unwrap();
        match parsed {
            Statement::Block { statements } => match statements[..] {
                [Statement::WhileStatement { .. }] => return,
                _ => panic!("unexpected statements in block (for loop)"),
            },
            _ => panic!("unexpected output for loop"),
        }
    }

    #[test]
    fn test_property_access() {
        let parsed = parse_expr("a.b").unwrap();
        assert_eq!(
            parsed,
            Expr::PropertyAccess {
                object: Box::new(Expr::Variable {
                    depth: None,
                    line: 1,
                    name: "a".to_string()
                }),
                name: "b".to_string(),
                line: 1,
            }
        );
    }

    #[test]
    fn test_class_declaration() {
        let parsed = parse_program("class Math {method(){}}").unwrap();
        assert_eq!(
            parsed[0],
            Statement::ClassDeclaration {
                name: "Math".to_string(),
                superclass: None,
                methods: vec![Statement::FunctionDeclaration {
                    name: "method".to_string(),
                    parameters: vec![],
                    body: vec![],
                    line: 1,
                }],
                line: 1,
            }
        );
    }

    #[test]
    fn test_class_declaration_with_superclass() {
        let parsed = parse_program("class Math < A {method(){}}").unwrap();
        assert_eq!(
            parsed[0],
            Statement::ClassDeclaration {
                name: "Math".to_string(),
                superclass: Some(Box::new(Expr::Variable {
                    name: "A".to_string(),
                    line: 1,
                    depth: None
                })),
                methods: vec![Statement::FunctionDeclaration {
                    name: "method".to_string(),
                    parameters: vec![],
                    body: vec![],
                    line: 1,
                }],
                line: 1,
            }
        );
    }
    #[test]
    fn test_class_declaration_unfinished() {
        let parsed = parse_program("class Math { method() {}");
        assert!(parsed.is_err());
        assert_eq!(
            parsed.unwrap_err(),
            vec![ParserError::MissingClosingBraceClass {
                lexeme: "end".to_string(),
                line: 1
            }]
        );
    }

    #[test]
    fn test_set_expression() {
        let parsed = parse_expr("breakfast.omelette.filling.meat = ham").unwrap();
        println!("{:#?}", parsed);
        assert_eq!(
            parsed,
            Expr::Set {
                object: Box::new(Expr::PropertyAccess {
                    object: Box::new(Expr::PropertyAccess {
                        object: Box::new(Expr::Variable {
                            depth: None,
                            line: 1,
                            name: "breakfast".to_string()
                        }),
                        name: "omelette".to_string(),
                        line: 1,
                    }),
                    name: "filling".to_string(),
                    line: 1,
                }),
                name: "meat".to_string(),
                line: 1,
                value: Box::new(Expr::Variable {
                    name: "ham".to_string(),
                    line: 1,
                    depth: None
                }),
            }
        );
    }
    #[test]
    fn test_program() {
        // let parsed = parse_program("print 2;").unwrap();
        let parsed = parse_program("// hello comment\nprint 1;\nprint 2;\n").unwrap();
        assert_eq!(parsed.len(), 2);
    }
}
