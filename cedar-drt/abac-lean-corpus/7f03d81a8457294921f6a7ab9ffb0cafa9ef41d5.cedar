permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (action.lessThan(r::Ahh2h::"", a::"mpl", !(!principal)))
};
