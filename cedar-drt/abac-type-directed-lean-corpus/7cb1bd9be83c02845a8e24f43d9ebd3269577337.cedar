@A33333S("")
@B("666")
permit(
  principal is z in z::"\0\0\0\0\0\0\0\0\070\0\06\0\0",
  action == Action::"66annotati",
  resource == A::"prin\u{1}\0\0\0\0\0\0\nci"
) when {
  ((true && ([] == false)) && false) && false
};
