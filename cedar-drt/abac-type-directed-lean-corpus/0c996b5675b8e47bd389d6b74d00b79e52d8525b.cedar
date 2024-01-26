permit(
  principal == a::"\\666",
  action == Action::"action",
  resource
) when {
  ((true && ({} has "\0\0\0\06")) && false) && (a::"" in a::"")
};
