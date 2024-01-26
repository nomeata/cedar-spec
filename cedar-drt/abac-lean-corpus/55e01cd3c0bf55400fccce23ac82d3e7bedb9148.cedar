permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"mpl"
) when {
  true && (action.lessThan(r::Ahh2h::"", a::"mpl", !(!context)))
};
