#include <visitor/visitor.h>
#include <core/list.h>

void visitAstNodeList(List *list, AstNodeVisitor *visitor) {
    if (list == NULL) {
        return;
    }

    ListNode *n;
    LIST_FOR_EACH(n, list->begin(list)) {
        AstNode *node = (AstNode *)DEREF_LIST_NODE(n);
        node->accept(node, visitor);
    }
}
